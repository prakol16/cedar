use std::collections::{HashMap, HashSet};

use cedar_policy::{PartialValue, EntityUid, ParsedEntity, EntityId, EntityTypeName, Value};
use ref_cast::RefCast;
use rusqlite::{Connection, Row, OptionalExtension, types::{FromSql, ValueRef}, Error};
use rusqlite::Error::FromSqlConversionFailure;


#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
struct SQLValue(Option<Value>);

impl FromSql for SQLValue {
    fn column_result(value: ValueRef<'_>) -> rusqlite::types::FromSqlResult<Self> {
        match value {
            ValueRef::Null => Ok(SQLValue(None)),
            ValueRef::Integer(x) => Ok(SQLValue(Some(x.into()))),
            // TODO: use decimal type
            ValueRef::Real(_) => Err(rusqlite::types::FromSqlError::InvalidType),
            ValueRef::Text(s) => {
                let decoded = std::str::from_utf8(s).map_err(|_| rusqlite::types::FromSqlError::InvalidType)?;
                Ok(SQLValue(Some(decoded.into())))
            },
            ValueRef::Blob(_) => Err(rusqlite::types::FromSqlError::InvalidType),
        }
    }
}


#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
pub struct EntitySQLId(EntityId);

impl EntitySQLId {
    pub fn id(self) -> EntityId { self.0 }
}

impl FromSql for EntitySQLId {
    fn column_result(value: ValueRef<'_>) -> rusqlite::types::FromSqlResult<Self> {
        match value {
            ValueRef::Integer(x) => Ok(EntitySQLId(x.to_string().parse().unwrap())),
            ValueRef::Text(_) => value.as_str().map(|v| EntitySQLId(v.parse().unwrap())),
            _ => Err(rusqlite::types::FromSqlError::InvalidType),
        }
    }
}

pub struct EntitySQLInfo<'e> {
    pub table: &'e str,
    pub id_attr: &'e str,
    pub sql_attr_names: Vec<&'e str>,
    pub attr_names: Vec<(usize, &'e str)>,
    pub ancestor_attr_ind: Option<usize>,
    query_string: String
}

impl<'e> EntitySQLInfo<'e> {
    pub fn new(table: &'e str, id_attr: &'e str, sql_attr_names: Vec<&'e str>, attr_names: Vec<(usize, &'e str)>, ancestor_attr_ind: Option<usize>) -> Self {
        let attr_names_string: String =
            if sql_attr_names.is_empty() { "*".into() }
            else { sql_attr_names.iter().map(|x| format!("\"{}\"", x)).collect::<Vec<String>>().join(", ") };
        Self {
            table,
            id_attr,
            sql_attr_names,
            attr_names,
            ancestor_attr_ind,
            query_string: format!("SELECT {} FROM \"{}\" WHERE \"{}\" = ?", attr_names_string, table, id_attr)
        }
    }

    pub fn simple(table: &'e str, attr_names: Vec<&'e str>, ancestor_attr: Option<&'e str>) -> Self {
        let mut sql_attr_names: Vec<&'e str> = attr_names.clone();
        if let Some(ancestor_attr) = ancestor_attr {
            sql_attr_names.push(ancestor_attr);
        }

        let len = attr_names.len();
        let attr_names: Vec<(usize, &'e str)> = attr_names.into_iter().enumerate().collect();

        Self::new(table, "uid", sql_attr_names, attr_names, ancestor_attr.map(|_| len))
    }

    pub fn make_entity_ancestors(&self, conn: &Connection, uid: &EntityUid) -> Result<Option<ParsedEntity>, rusqlite::Error> {
        self.make_entity(conn, uid, |row| {
            match self.ancestor_attr_ind {
                Some(ancestors_attr_ind) => {
                    serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(ancestors_attr_ind)?)
                    .map_err(|e| FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e)))?
                    .as_array().ok_or(rusqlite::Error::InvalidQuery)? // TODO: make an error type
                    .iter()
                    .map(|x| {
                        EntityUid::from_json(x.clone()).map_err(|e| FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e)))
                    })
                    .collect()
                },
                None => panic!("make_entity_ancestors should only be called when `ancestors_attr_ind` is filled"),
            }
        })
    }

    pub fn get_query_string(&self) -> &str {
        return &self.query_string;
    }

    pub fn make_entity(&self, conn: &Connection, uid: &EntityUid, ancestors: impl FnOnce(&Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error>)
        -> Result<Option<ParsedEntity>, rusqlite::Error> {
        make_entity_from_table(conn, uid, &self.query_string,
            |row| convert_attr_names(row, &self.attr_names),
            ancestors)
    }

    pub fn make_entity_extra_attrs(&self, conn: &Connection, uid: &EntityUid, ancestors: impl FnOnce(&Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error>,
        extra_attrs: impl FnOnce(&Row<'_>) -> Result<HashMap<String, PartialValue>, rusqlite::Error>)
        -> Result<Option<ParsedEntity>, rusqlite::Error> {
        make_entity_from_table(conn, uid, &self.query_string,
            |row| {
                let mut attrs = convert_attr_names(row, &self.attr_names)?;
                attrs.extend(extra_attrs(row)?);
                Ok(attrs)
            }, ancestors)
    }
}

pub struct AncestorSQLInfo<'e> {
    pub table: &'e str,
    pub child_id: &'e str,
    pub parent_id: &'e str,
    query_string: String
}

impl<'e> AncestorSQLInfo<'e> {
    pub fn new(table: &'e str, child_id: &'e str, parent_id: &'e str) -> Self {
        Self {
            table,
            child_id,
            parent_id,
            query_string: format!("SELECT \"{}\" FROM \"{}\" WHERE \"{}\" = ?", parent_id, table, child_id)
        }
    }

    pub fn get_ancestors(&self, conn: &Connection, id: &EntityId, tp: &EntityTypeName) -> Result<HashSet<EntityUid>, rusqlite::Error> {
        let mut stmt = conn.prepare(&self.query_string)?;
        let result = stmt.query_map(&[id.as_ref()], |row| -> Result<EntityUid, Error> {
            let parent_id: EntitySQLId = row.get(0)?;
            Ok(EntityUid::from_type_name_and_id(tp.clone(), parent_id.0))
        });
        match result {
            Ok(x) => x.collect::<Result<HashSet<EntityUid>, Error>>(),
            Err(e) => Err(e),
        }
    }
}

pub fn convert_attr_names(query_result: &Row, attr_names: &[(usize, &str)]) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
    attr_names.iter()
        .filter_map(|(ind, nm)| {
            match query_result.get::<_, SQLValue>(*ind) {
                Ok(SQLValue(Some(v))) => Some(Ok((nm.to_string(), v.into()))),
                Ok(SQLValue(None)) => None,
                Err(e) => Some(Err(e)),
            }
        })
        .collect()
}

pub fn make_entity_from_table(conn: &Connection, uid: &EntityUid,
    query_string: &str,
    attrs: impl FnOnce(&Row<'_>) -> Result<HashMap<String, PartialValue>, rusqlite::Error>,
    ancestors: impl FnOnce(&Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error>) -> Result<Option<ParsedEntity>, rusqlite::Error> {
    conn.query_row_and_then(query_string, &[uid.id().as_ref()], |row| {
        Ok::<ParsedEntity, rusqlite::Error>(ParsedEntity::new(uid.clone(), attrs(row)?, ancestors(row)?))
    })
    .optional()
}
