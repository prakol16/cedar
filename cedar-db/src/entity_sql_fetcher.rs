use std::{collections::{HashMap, HashSet}, borrow::Cow};

use cedar_policy::{EntityTypeName, PartialValue, EntityUid, EntityId, EntityDatabase, Mode, ParsedEntity};
use ref_cast::RefCast;
use rusqlite::{Connection, Row, OptionalExtension, types::{FromSql, ValueRef}};


pub struct EntityFetchTable<T: EntityFetcher>(pub HashMap<EntityTypeName, T>);

pub trait EntityFetcher {
    fn get<'e>(&'e self, uid: &EntityId) -> Option<(HashMap<String, PartialValue>, HashSet<EntityUid>)>;
}

impl<T: EntityFetcher> EntityDatabase for EntityFetchTable<T> {
    fn get<'e>(&'e self, uid: &EntityUid) -> Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>> {
        let (attrs, parents) = self.0.get(&uid.type_name())?.get(uid.id())?;
        Some(Cow::Owned(ParsedEntity::new(uid.clone(), attrs, parents)))
    }

    fn partial_mode(&self) -> cedar_policy::Mode {
        Mode::Partial
    }
}

pub struct EntitySQLFetcher<'e, T: EntitySQLAttrConverter = EntitySQLAttrConverterImpl<'e>> {
    conn: &'e Connection,
    table_name: &'e str,
    attr_names: String,
    converter: T,
}

impl<'e, T: EntitySQLAttrConverter> EntitySQLFetcher<'e, T> {
    pub fn new(conn: &'e Connection, table_name: &'e str, attr_names: &[&str], converter: T) -> Self {
        let attr_names_string: String = attr_names.iter().map(|x| format!("\"{}\"", x)).collect::<Vec<String>>().join(", ");
        Self {
            conn,
            table_name,
            attr_names: attr_names_string,
            converter
        }
    }
}

impl<'a, T: EntitySQLAttrConverter> EntityFetcher for EntitySQLFetcher<'a, T> {
    fn get<'e>(&'e self, id: &EntityId) -> Option<(HashMap<String, PartialValue>, HashSet<EntityUid>)> {
        // TODO: escape attr names and table_name?
        let query = format!("SELECT {} FROM \"{}\" WHERE uid = ?", self.attr_names, self.table_name);
        let attrs: Option<HashMap<String, PartialValue>> = self.conn.query_row(&query,
            &[id.as_ref()], |row| self.converter.convert(row))
            .optional().expect("SQL query failed");  // TODO: if panic, return a result (maybe make return type Result<Option<...>>?)
        Some((attrs?, HashSet::new()))
    }
}

impl<'e> EntitySQLFetcher<'e> {
    pub fn new_default(conn: &'e Connection, table_name: &'e str, attr_names: &[&'e str]) -> Self {
        EntitySQLFetcher::new(
            conn,
            table_name,
            attr_names,
            EntitySQLAttrConverterImpl::of_names(attr_names)
        )
    }
}

pub trait EntitySQLAttrConverter {
    // TODO: make our own error type?
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error>;
}

pub struct EntitySQLAttrConverterImpl<'e> {
    // TODO: allow type checking?
    attr_names: Vec<(usize, &'e str)>,
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

impl<'e> EntitySQLAttrConverterImpl<'e> {
    pub fn new(attr_names: Vec<(usize, &'e str)>) -> Self {
        Self {
            attr_names
        }
    }

    pub fn of_names(attr_names: &[&'e str]) -> Self {
        Self {
            attr_names: attr_names.into_iter().enumerate().map(|(n, v)| (n, *v)).collect()
        }
    }
}

impl<'e> EntitySQLAttrConverter for EntitySQLAttrConverterImpl<'e> {
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
