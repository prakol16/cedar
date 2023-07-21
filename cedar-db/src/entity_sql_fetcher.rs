use std::{collections::{HashMap, HashSet}, borrow::Cow};

use cedar_policy::{EntityTypeName, PartialValue, EntityUid, EntityDatabase, ParsedEntity, Mode};
use ref_cast::RefCast;
use rusqlite::{Connection, Row, OptionalExtension, types::{FromSql, ValueRef}};


pub struct EntitySQLFetchTable {
    conn: Connection,
    table: &'static HashMap<EntityTypeName, EntitySQLTypeFetcher>
}

pub struct EntitySQLTypeFetcher {
    table_name: &'static str,
    attr_names: Vec<&'static str>,
    converter: Box<dyn EntitySQLAttrConverter + Send + Sync>,
}

impl EntitySQLTypeFetcher {
    pub fn new(table_name: &'static str, attr_names: Vec<&'static str>, converter:  Box<dyn EntitySQLAttrConverter + Send + Sync>) -> Self {
        Self {
            table_name,
            attr_names,
            converter
        }
    }

    pub fn new_default(table_name: &'static str, attr_names: &[&'static str]) -> Self {
        Self {
            table_name,
            attr_names: attr_names.into(),
            converter: Box::new(EntitySQLAttrConverterImpl::of_names(attr_names))
        }
    }
}

pub trait EntitySQLAttrConverter {
    // TODO: make our own error type?
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error>;
}

impl EntitySQLFetchTable {
    pub fn new(conn: Connection, table: &'static HashMap<EntityTypeName, EntitySQLTypeFetcher>) -> Self {
        Self {
            conn,
            table
        }
    }
}

pub struct EntitySQLAttrConverterImpl {
    // TODO: allow type checking?
    attr_names: Vec<(usize, &'static str)>,
}

#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
struct SQLPartialValue(Option<PartialValue>);

impl FromSql for SQLPartialValue {
    fn column_result(value: ValueRef<'_>) -> rusqlite::types::FromSqlResult<Self> {
        match value {
            ValueRef::Null => Ok(SQLPartialValue(None)),
            ValueRef::Integer(x) => Ok(SQLPartialValue(Some(x.into()))),
            // TODO: use decimal type
            ValueRef::Real(_) => Err(rusqlite::types::FromSqlError::InvalidType),
            ValueRef::Text(s) => {
                let decoded = std::str::from_utf8(s).map_err(|_| rusqlite::types::FromSqlError::InvalidType)?;
                Ok(SQLPartialValue(Some(decoded.into())))
            },
            ValueRef::Blob(_) => Err(rusqlite::types::FromSqlError::InvalidType),
        }
    }
}

impl EntitySQLAttrConverterImpl {
    pub fn new(attr_names: Vec<(usize, &'static str)>) -> Self {
        Self {
            attr_names
        }
    }

    pub fn of_names(attr_names: &[&'static str]) -> Self {
        Self {
            attr_names: attr_names.into_iter().enumerate().map(|(n, v)| (n, *v)).collect()
        }
    }
}

impl EntitySQLAttrConverter for EntitySQLAttrConverterImpl {
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
        self.attr_names.iter()
            .filter_map(|(ind, nm)| {
                match query_result.get::<_, SQLPartialValue>(*ind) {
                    Ok(SQLPartialValue(Some(v))) => Some(Ok((nm.to_string(), v))),
                    Ok(SQLPartialValue(None)) => None,
                    Err(e) => Some(Err(e)),
                }
            })
            .collect()
    }
}

impl EntityDatabase for EntitySQLFetchTable {
    fn get<'e>(&'e self, uid: &EntityUid) -> Option<Cow<'e, ParsedEntity>> {
        let type_fetcher = self.table.get(&uid.type_name())?;
        // TODO: escape attr names and table_name?
        let query = format!("SELECT {} FROM \"{}\" WHERE uid = ?",
            type_fetcher.attr_names
            .iter()
            .map(|x| format!("\"{}\"", x))
            .collect::<Vec<String>>()
            .join(", "), type_fetcher.table_name);
        let result: Option<HashMap<String, PartialValue>> = self.conn.query_row(&query,
            &[uid.id().as_ref()], |row| type_fetcher.converter.convert(row))
            .optional().expect("SQL query failed");  // TODO: if panic, return a result (maybe make return type Result<Option<...>>?)
        result.map(|attrs| Cow::Owned(ParsedEntity::new(uid.clone(), attrs, HashSet::new())))
    }

    fn partial_mode(&self) -> Mode {
        Mode::Partial
    }
}
