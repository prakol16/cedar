//! In this module, we provide helper functions to dump the contents
//! of a schema and a database to a SQL database
//! This is particularly useful for testing or for migrating from
//! a JSON-based store to a SQL-based store

use std::collections::HashMap;

use cedar_policy::{Schema, EntityTypeName};

use cedar_policy_validator::{types::{Type, EntityRecordKind}, ValidatorEntityType};
use ref_cast::RefCast;
use sea_query::{TableCreateStatement, Table, Iden, ColumnDef, ColumnType, Alias, ForeignKey, ForeignKeyCreateStatement, IntoTableRef, TableRef, IntoIden, PostgresQueryBuilder};
use smol_str::SmolStr;
use thiserror::Error;

use crate::query_expr::{QueryExprError, QueryType, QueryPrimitiveType};

#[derive(Debug, Error)]
pub enum DumpEntitiesError {
    #[error("Entity type {0} not found in schema")]
    EntityTypeNotFound(EntityTypeName),
    #[error("Error in type conversion: {0}")]
    QueryExprError(#[from] QueryExprError),
    #[error("Missing entity type {0} in id map")]
    MissingIdInMap(EntityTypeName),
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
        const CHILD_UID: &str = "child_uid";
        const PARENT_UID: &str = "parent_uid";
        table.col(ColumnDef::new(Alias::new(CHILD_UID)).text().not_null());
        table.col(ColumnDef::new(Alias::new(PARENT_UID)).text().not_null());

        let child_fk = id_map.get(&echild).ok_or_else(|| DumpEntitiesError::MissingIdInMap(echild.clone()))?.as_str();
        let parent_fk = id_map.get(&eparent).ok_or_else(|| DumpEntitiesError::MissingIdInMap(eparent.clone()))?.as_str();
        table.foreign_key(ForeignKey::create()
            .from(table_name.clone(), Alias::new(CHILD_UID))
            .to(EntityTableIden(echild.clone()), Alias::new(child_fk))
        );
        table.foreign_key(ForeignKey::create()
            .from(table_name.clone(), Alias::new(PARENT_UID))
            .to(EntityTableIden(eparent.clone()), Alias::new(parent_fk))
        );
        result.push(table);
    }
    Ok(())
}

/// Create all the tables necessary in `schema`, including the foreign key constraints
/// (Note: the ancestry tables already have the foreign key constraints included in the table)
pub fn create_tables(schema: &Schema) -> Result<(Vec<TableCreateStatement>, Vec<ForeignKeyCreateStatement>)> {
    let mut entity_tables = Vec::new();
    let mut foreign_keys = Vec::new();
    let mut ancestry_tables = Vec::new();
    let id_map = create_id_map(schema);
    for (name, ty) in schema.0.entity_types() {
        create_table_from_entity_type(ty, EntityTypeName::ref_cast(name), &id_map, &mut entity_tables, &mut foreign_keys)?;
        create_ancestry_table(ty, EntityTypeName::ref_cast(name), &id_map, &mut ancestry_tables)?;
    }
    Ok((entity_tables.into_iter().chain(ancestry_tables).collect(), foreign_keys))
}

/// Create all the tables necessary in `schema`, including the foreign key constraints
/// as postgresql statements
pub fn create_tables_postgres(schema: &Schema) -> Result<Vec<String>> {
    let (tables, fks) = create_tables(schema)?;
    let result = tables.into_iter()
        .map(|t| t.to_string(PostgresQueryBuilder))
        .chain(
            fks.into_iter()
                .map(|fk| fk.to_string(PostgresQueryBuilder))
        )
        .collect();
    Ok(result)
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use cedar_policy::Schema;
    use sea_query::PostgresQueryBuilder;

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
        let (tables, fks) = create_tables(&schema).expect("Should not fail to create tables");
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
}

