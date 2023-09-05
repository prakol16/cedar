//! In this module, we provide helper functions to dump the contents
//! of a schema and a database to a SQL database
//! This is particularly useful for testing or for migrating from
//! a JSON-based store to a SQL-based store

use std::collections::HashMap;

use cedar_policy::{Schema, EntityTypeName, PartialValue};

use cedar_policy_core::{entities::Entities, ast::{Entity, EntityUID}};
use cedar_policy_validator::{types::{Type, EntityRecordKind, AttributeType}, ValidatorEntityType};
use ref_cast::RefCast;
use sea_query::{TableCreateStatement, Table, Iden, ColumnDef, ColumnType, Alias, ForeignKey, ForeignKeyCreateStatement, IntoTableRef, TableRef, IntoIden, PostgresQueryBuilder, InsertStatement, Query};
use smol_str::SmolStr;
use thiserror::Error;

use crate::{query_expr::{QueryExprError, QueryType, QueryPrimitiveType}, sql_common::{null_value_of_type, value_to_sea_query_value}};

#[derive(Debug, Error)]
pub enum DumpEntitiesError {
    #[error("Entity type {0} not found in schema")]
    EntityTypeNotFound(EntityTypeName),
    #[error("Entity type {0} or {1} not found in schema")]
    EntityTypeNotFound2(EntityTypeName, EntityTypeName),
    #[error("Error in type conversion: {0}")]
    QueryExprError(#[from] QueryExprError),
    #[error("Missing entity type {0} in id map")]
    MissingIdInMap(EntityTypeName),
    #[error("Entity supplied with unknown entity type")]
    UnknownEntityType,
    #[error("Sea query error: {0}")]
    SeaQueryError(#[from] sea_query::error::Error),
}

type Result<T> = std::result::Result<T, DumpEntitiesError>;

#[derive(Iden)]
#[iden = "cedar"]
pub struct CedarSQLSchemaName;

/// The name of the table for a given entity type
/// The name of the table will be "entity_{entity_type}"
#[derive(Debug, Clone, PartialEq, Eq, Hash, RefCast)]
#[repr(transparent)]
pub struct EntityTableIden(EntityTypeName);

impl EntityTableIden {
    /// Create a new table from `entity_type`
    /// The table name will be "entity_{entity_type}"
    pub fn new(entity_type: EntityTypeName) -> Self {
        Self(entity_type)
    }
}

impl IntoTableRef for EntityTableIden {
    fn into_table_ref(self) -> TableRef {
        TableRef::SchemaTable(CedarSQLSchemaName.into_iden(),
            Alias::new(format!("entity_{}", self.0)).into_iden())
    }
}

#[derive(Debug, Clone)]
pub struct EntityAncestryTableIden {
    child: EntityTypeName,
    parent: EntityTypeName,
    escaped_str: String
}

impl EntityAncestryTableIden {
    /// Create a new table from `child` and `parent`
    /// We ensure that the table representation is an injective function of (child, parent)
    /// so that two different (child, parent) pairs will necessarily have different table names
    /// By default, the table name will be "ancestry_{child}_,_{parent}"
    pub fn new(child: EntityTypeName, parent: EntityTypeName) -> Self {
        let child_str = child.to_string();
        let parent_str = parent.to_string();
        let comma_count = child_str.matches(',').count() + parent_str.matches(',').count();
        // This process is reversible by looking at the longest chain of commas
        // and splitting the string at that point
        // By surrounding the commas with underscores, we ensure that the separator is uniquely identifiable
        let escaped_str = ",".repeat(comma_count + 1);
        Self {
            child,
            parent,
            escaped_str
        }
    }
}

impl IntoTableRef for EntityAncestryTableIden {
    fn into_table_ref(self) -> TableRef {
        TableRef::SchemaTable(CedarSQLSchemaName.into_iden(),
            Alias::new(format!("ancestry_{}_{}_{}", self.child, self.escaped_str, self.parent)).into_iden())
    }
}

impl From<QueryPrimitiveType> for ColumnType {
    fn from(value: QueryPrimitiveType) -> Self {
        match value {
            QueryPrimitiveType::Bool => ColumnType::Boolean,
            QueryPrimitiveType::Long => ColumnType::BigInteger,
            QueryPrimitiveType::StringOrEntity => ColumnType::Text,
            QueryPrimitiveType::Record => ColumnType::JsonBinary,
        }
    }
}

impl From<QueryType> for ColumnType {
    fn from(value: QueryType) -> Self {
        match value {
            QueryType::Primitive(ty) => ty.into(),
            QueryType::Array(ty) => ColumnType::Array(sea_query::RcOrArc::new(ty.into())),
        }
    }
}

pub fn create_id_map(schema: &Schema) -> HashMap<EntityTypeName, SmolStr> {
    let uid_smolstr = SmolStr::from("uid");
    schema.0.entity_types()
        .map(|(name, v)| {
            if v.attr(uid_smolstr.as_str()).is_some() {
                return (EntityTypeName::ref_cast(name).clone(), uid_smolstr.clone());
            }
            let mut uid_str: String = uid_smolstr.to_string();
            while v.attr(&uid_str).is_some() {
                uid_str.push('!'); // add escape character ! until we don't have a collision
            }
            (EntityTypeName::ref_cast(name).clone(), SmolStr::from(uid_str))
        })
        .collect()
}

/// Creates a table for a given entity type in the schema
/// The table will have columns matching the attributes of the entity type, as well as a text type column for the id, whose name is given in id_map
/// The table will be named "entity_{entity_type}"
/// In addition, we separately add foreign key constraints for the tables (which can be added after all the tables are created)
pub fn create_table_from_entity_type(entity_type: &ValidatorEntityType, ety: &EntityTypeName, id_map: &HashMap<EntityTypeName, SmolStr>, result: &mut Vec<TableCreateStatement>, foreign_keys: &mut Vec<ForeignKeyCreateStatement>) -> Result<()> {
    let mut table = Table::create();
    let table_name = EntityTableIden(ety.clone());
    table.table(table_name.clone());

    let uid_str = id_map.get(ety).ok_or_else(|| DumpEntitiesError::MissingIdInMap(ety.clone()))?.as_str();
    table.col(ColumnDef::new_with_type(Alias::new(uid_str), ColumnType::Text).primary_key());

    for (attr, tp) in entity_type.attributes() {
        let mut new_col = ColumnDef::new_with_type(Alias::new(attr.as_str()), QueryType::try_from(&tp.attr_type)?.into());
        if tp.is_required {
            new_col.not_null();
        }
        table.col(&mut new_col);
        if let Type::EntityOrRecord(EntityRecordKind::Entity(lub)) = &tp.attr_type {
            let foreign_tp = EntityTypeName::ref_cast(lub.get_single_entity().ok_or(QueryExprError::GetAttrLUBNotSingle)?);
            let foreign_uid = id_map.get(&foreign_tp).ok_or_else(|| DumpEntitiesError::MissingIdInMap(foreign_tp.clone()))?.as_str();
            let mut foreign_key = ForeignKey::create();
            foreign_key.from(table_name.clone(), Alias::new(uid_str));
            foreign_key.to(EntityTableIden(foreign_tp.clone()), Alias::new(foreign_uid));
            foreign_keys.push(foreign_key);
        }
    }
    result.push(table);
    Ok(())
}

#[derive(Iden)]
pub enum AncestryCols {
    #[iden = "child_uid"]
    Descendant,
    #[iden = "parent_uid"]
    Ancestor,
}

/// Creates a table for the descendants of the given entity type in the schema
/// Note: these tables already have foreign key constraints attached to them, so they should be created
/// after the entity tables have been created
pub fn create_ancestry_table(entity_type: &ValidatorEntityType, eparent: &EntityTypeName, id_map: &HashMap<EntityTypeName, SmolStr>, result: &mut Vec<TableCreateStatement>) -> Result<()> {
    for child in entity_type.descendants.iter() {
        let mut table = Table::create();
        let echild = EntityTypeName::ref_cast(child);
        let table_name = EntityAncestryTableIden::new(echild.clone(), eparent.clone());
        table.table(table_name.clone());

        // Create two columns for the child and parent ids
        table.col(ColumnDef::new(AncestryCols::Descendant).text().not_null());
        table.col(ColumnDef::new(AncestryCols::Ancestor).text().not_null());

        let child_fk = id_map.get(&echild).ok_or_else(|| DumpEntitiesError::MissingIdInMap(echild.clone()))?.as_str();
        let parent_fk = id_map.get(&eparent).ok_or_else(|| DumpEntitiesError::MissingIdInMap(eparent.clone()))?.as_str();
        table.foreign_key(ForeignKey::create()
            .from(table_name.clone(), AncestryCols::Descendant)
            .to(EntityTableIden(echild.clone()), Alias::new(child_fk))
        );
        table.foreign_key(ForeignKey::create()
            .from(table_name.clone(), AncestryCols::Ancestor)
            .to(EntityTableIden(eparent.clone()), Alias::new(parent_fk))
        );
        result.push(table);
    }
    Ok(())
}

/// Create all the tables necessary in `schema`, including the foreign key constraints
/// (Note: the ancestry tables already have the foreign key constraints included in the table)
/// Then return the statements necessary to populate the tables
/// as well as the "id map" used for the tables (i.e. the column name for the id of each entity type)
pub fn create_tables(entities: &Entities<PartialValue>, schema: &Schema) -> Result<(Vec<TableCreateStatement>, Vec<ForeignKeyCreateStatement>, Vec<InsertStatement>, HashMap<EntityTypeName, SmolStr>)> {
    let mut entity_tables = Vec::new();
    let mut foreign_keys = Vec::new();
    let mut ancestry_tables = Vec::new();
    let id_map = create_id_map(schema);
    for (name, ty) in schema.0.entity_types() {
        create_table_from_entity_type(ty, EntityTypeName::ref_cast(name), &id_map, &mut entity_tables, &mut foreign_keys)?;
        create_ancestry_table(ty, EntityTypeName::ref_cast(name), &id_map, &mut ancestry_tables)?;
    }
    let mut inserts = populate_attr_tables(entities, schema, &id_map)?;
    inserts.extend(populate_ancestry_tables(entities, schema)?);
    Ok((entity_tables.into_iter().chain(ancestry_tables).collect(), foreign_keys, inserts, id_map))
}

/// Add the entity to the insert statement
/// The first value is assumed to be the id; the rest of the attributes will be filled in according to `attrs`
fn add_entity_attrs_to_insert<'e, T: Iterator<Item = (&'e SmolStr, &'e AttributeType)>>(entity: &Entity<PartialValue>, insert: &mut InsertStatement, attrs: T) -> Result<()> {
    let uid = entity.uid();
    let id: &str = uid.eid().as_ref();
    let values: Vec<sea_query::SimpleExpr> =
    std::iter::once(Ok(id.into()))
    .chain(
        attrs
        .map(|(attr, ty)| {
            let value = entity.get(attr);
            let ty = QueryType::try_from(&ty.attr_type)?;
            match value {
                Some(PartialValue::Residual(_)) | None => Ok(null_value_of_type(ty)),
                Some(PartialValue::Value(v)) => Ok(value_to_sea_query_value(v, ty)),
            }
        })
        .map(|v| v.map(|v| v.into()))
    ).collect::<Result<_>>()?;
    insert.values(values)?;
    Ok(())
}

/// Add the relationship to the insert statements
fn add_relationship(inserts: &mut HashMap<(EntityTypeName, EntityTypeName), InsertStatement>, child: &EntityUID, parent: &EntityUID) -> Result<()> {
    match (child.entity_type(), parent.entity_type()) {
        (cedar_policy_core::ast::EntityType::Concrete(child_ty), cedar_policy_core::ast::EntityType::Concrete(parent_ty)) => {
            let echild = EntityTypeName::ref_cast(child_ty);
            let eparent = EntityTypeName::ref_cast(parent_ty);
            let child_id: &str = child.eid().as_ref();
            let parent_id: &str = parent.eid().as_ref();
            inserts.get_mut(&(echild.clone(), eparent.clone()))
                .ok_or_else(|| DumpEntitiesError::EntityTypeNotFound2(echild.clone(), eparent.clone()))?
                .values([child_id.into(), parent_id.into()])?;
            Ok(())
        },
        _ => Err(DumpEntitiesError::UnknownEntityType)
    }
}

/// Populate the entity tables with the given entities' attributes
pub fn populate_attr_tables(entities: &Entities<PartialValue>, schema: &Schema, id_map: &HashMap<EntityTypeName, SmolStr>) -> Result<Vec<InsertStatement>> {
    let mut inserts: HashMap<EntityTypeName, InsertStatement> = HashMap::new();
    for (ty, attrs) in schema.0.entity_types() {
        let mut insert = Query::insert();
        let ty = EntityTypeName::ref_cast(ty);
        insert.into_table(EntityTableIden(ty.clone()));

        let id_col_name = id_map.get(&ty).ok_or_else(|| DumpEntitiesError::MissingIdInMap(ty.clone()))?;
        insert.columns(std::iter::once(Alias::new(id_col_name.as_str()))
            .chain(attrs.attributes().map(|(k, _)| Alias::new(k.as_str()))));
        inserts.insert(ty.clone(), insert);
    }
    for entity in entities.iter() {
        let uid = entity.uid();
        let entity_type_name = match uid.entity_type() {
            cedar_policy_core::ast::EntityType::Concrete(n) => n,
            cedar_policy_core::ast::EntityType::Unspecified => return Err(DumpEntitiesError::UnknownEntityType),
        };
        let eentity_type_name = EntityTypeName::ref_cast(entity_type_name);
        let entity_type = schema.0.get_entity_type(entity_type_name)
            .ok_or_else(|| DumpEntitiesError::EntityTypeNotFound(eentity_type_name.clone()))?;
        let insert = inserts.get_mut(&eentity_type_name).expect("Existence of entity type checked should have been checked above");
        add_entity_attrs_to_insert(entity, insert, entity_type.attributes())?;
    }
    Ok(inserts.into_values().collect())
}

/// Populate the ancestry tables with the given entities' ancestry information
pub fn populate_ancestry_tables(entities: &Entities<PartialValue>, schema: &Schema) -> Result<Vec<InsertStatement>> {
    let mut inserts: HashMap<(EntityTypeName, EntityTypeName), InsertStatement> = HashMap::new();
    for (name, ty) in schema.0.entity_types() {
        let eparent = EntityTypeName::ref_cast(name);
        for child in ty.descendants.iter() {
            let echild = EntityTypeName::ref_cast(child);
            let mut insert = Query::insert();
            insert.into_table(EntityAncestryTableIden::new(echild.clone(), eparent.clone()));
            insert.columns([AncestryCols::Descendant, AncestryCols::Ancestor]);
            inserts.insert((echild.clone(), eparent.clone()), insert);
        }
    }

    for entity in entities.iter() {
        for parent in entity.ancestors() {
            add_relationship(&mut inserts, &entity.uid(), parent)?;
        }
    }
    Ok(inserts.into_values().collect())
}


/// Create all the tables necessary in `schema`, including the foreign key constraints
/// as postgresql statements; also returns the id map
pub fn create_tables_postgres(entities: &Entities<PartialValue>, schema: &Schema) -> Result<(Vec<String>, HashMap<EntityTypeName, SmolStr>)> {
    let (tables, fks, inserts, id_map) = create_tables(entities, schema)?;
    let result = tables.into_iter()
        .map(|t| t.to_string(PostgresQueryBuilder))
        .chain(
            fks.into_iter()
                .map(|fk| fk.to_string(PostgresQueryBuilder))
        )
        .chain(
            inserts.into_iter()
                .map(|insert| insert.to_string(PostgresQueryBuilder))
        )
        .collect();
    Ok((result, id_map))
}

#[cfg(test)]
mod test {
    use std::collections::{HashSet, HashMap};

    use cedar_policy::{Schema, PartialValue};
    use cedar_policy_core::{entities::Entities, ast::Entity};
    use sea_query::PostgresQueryBuilder;

    use crate::dump_entities::create_tables_postgres;

    use super::create_tables;

    fn get_schema() -> Schema {
        r#"
        {
            "": {
                "entityTypes": {
                    "Users": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "name": {
                                    "type": "String"
                                },
                                "age": {
                                    "type": "Long"
                                },
                                "location": {
                                    "type": "String",
                                    "required": false
                                }
                            }
                        },
                        "memberOfTypes": ["Users"]
                    },
                    "Photos": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "title": {
                                    "type": "String"
                                },
                                "user_id": {
                                    "type": "Entity",
                                    "name": "Users"
                                }
                            }
                        }
                    }
                },
                "actions": {
                    "view": {
                        "appliesTo": {
                            "principalTypes": ["Users"],
                            "resourceTypes": ["Photos"]
                        }
                    }
                }
            }
        }
        "#.parse().expect("Schema should not fail to parse")
    }

    #[test]
    fn test_create_from_schema() {
        let schema = get_schema();
        let (tables, fks, _, _) = create_tables(&Entities::new(), &schema).expect("Should not fail to create tables");
        let result = tables.into_iter()
            .map(|t| t.to_string(PostgresQueryBuilder))
            .chain(
                fks.into_iter()
                    .map(|fk| fk.to_string(PostgresQueryBuilder))
            )
            .collect::<HashSet<_>>();
        assert!(result == HashSet::from([
            r#"CREATE TABLE "cedar"."entity_Users" ( "uid" text PRIMARY KEY, "age" bigint NOT NULL, "location" text, "name" text NOT NULL )"#.into(),
            r#"CREATE TABLE "cedar"."entity_Photos" ( "uid" text PRIMARY KEY, "title" text NOT NULL, "user_id" text NOT NULL )"#.into(),
            r#"CREATE TABLE "cedar"."ancestry_Users_,_Users" ( "child_uid" text NOT NULL, "parent_uid" text NOT NULL, FOREIGN KEY ("child_uid") REFERENCES "cedar"."entity_Users" ("uid"), FOREIGN KEY ("parent_uid") REFERENCES "cedar"."entity_Users" ("uid") )"#.into(),
            r#"ALTER TABLE "cedar"."entity_Photos" ADD FOREIGN KEY ("uid") REFERENCES "cedar"."entity_Users" ("uid")"#.into()
        ]));
    }


    #[test]
    fn test_unicode_zero() {
        let schema = get_schema();
        let entities = Entities::from_entities(
            [
                Entity::new("Users::\"\0\"".parse().unwrap(),
                    HashMap::from([
                        ("name".into(), PartialValue::from("")),
                        ("age".into(), PartialValue::from(0))
                    ]), HashSet::new())
            ],
            cedar_policy_core::entities::TCComputation::ComputeNow
        ).expect("Should not fail to create entities");
        create_tables_postgres(&entities, &schema)
        // In theory this should actually fail since postgres cannot handle null unicode characters
        // TODO: maybe make a sea query issue?
            .expect_err("Should fail to create table with unicode zero");
    }
}

