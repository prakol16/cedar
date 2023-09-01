//! In this module, we provide helper functions to dump the contents
//! of a schema and a database to a SQL database
//! This is particularly useful for testing or for migrating from
//! a JSON-based store to a SQL-based store

use std::{fmt, collections::HashMap};

use cedar_policy::{Schema, EntityTypeName};
use cedar_policy_core::ast::Name;
use cedar_policy_validator::types::{Type, EntityRecordKind};
use ref_cast::RefCast;
use sea_query::{TableCreateStatement, Table, Iden, ColumnDef, ColumnType, Alias, ForeignKey};
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

/// The name of the table for a given entity type
/// The name of the table will be "entity_{entity_type}"
#[derive(Debug, Clone, PartialEq, Eq, Hash, RefCast)]
#[repr(transparent)]
pub struct EntityTableIden(EntityTypeName);

impl Iden for EntityTableIden {
    fn unquoted(&self,s: &mut dyn fmt::Write) {
        write!(s, "entity_{}", self.0).unwrap();
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
    /// We ensure that escaped_str is an injective function of (child, parent)
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

impl Iden for EntityAncestryTableIden {
    fn unquoted(&self, s: &mut dyn fmt::Write) {
        write!(s, "ancestry_{}_{}_{}", self.child, self.escaped_str, self.parent).unwrap();
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
/// The table will have columns matching the attributes of the entity type, as well as a text type column "uid"
/// The table will be named "entity_{entity_type}"
/// Returns the name of the id column of the table (which may be different from "uid" if there are existing attributes called "uid")
pub fn create_table_from_entity_type(schema: &Schema, ty: &Name, id_map: HashMap<EntityTypeName, SmolStr>, result: &mut Vec<TableCreateStatement>) -> Result<()> {
    let ety = EntityTypeName::ref_cast(ty);
    let entity_type = schema.0.get_entity_type(ty).ok_or_else(|| DumpEntitiesError::EntityTypeNotFound(ety.clone()))?;
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
            table.foreign_key(ForeignKey::create()
                .from(table_name.clone(), Alias::new(uid_str))
                .to(EntityTableIden(foreign_tp.clone()), Alias::new(foreign_uid))
            );
        }
    }
    result.push(table);
    Ok(())
}

pub fn create_ancestry_table(schema: &Schema, ty: &Name, id_map: HashMap<EntityTypeName, SmolStr>, result: &mut Vec<TableCreateStatement>) -> Result<()> {
    let eparent = EntityTypeName::ref_cast(ty);
    let entity_type = schema.0.get_entity_type(ty).ok_or_else(|| DumpEntitiesError::EntityTypeNotFound(eparent.clone()))?;
    for child in entity_type.descendants.iter() {
        let mut table = Table::create();
        let echild = EntityTypeName::ref_cast(child);
        let table_name = EntityAncestryTableIden::new(echild.clone(), eparent.clone());
        table.table(table_name.clone());

        // Create two columns for the child and parent ids
        const CHILD_UID: &str = "child_uid";
        const PARENT_UID: &str = "parent_uid";
        table.col(ColumnDef::new(Alias::new(CHILD_UID)).not_null());
        table.col(ColumnDef::new(Alias::new(PARENT_UID)).not_null());

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
