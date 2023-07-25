use std::{collections::{HashMap, HashSet}, borrow::Cow};

use cedar_policy::{EntityTypeName, PartialValue, EntityUid, EntityId, EntityDatabase, Mode, ParsedEntity};
use ref_cast::RefCast;
use rusqlite::{Connection, Row, OptionalExtension, types::{FromSql, ValueRef}};
use rusqlite::Error::FromSqlConversionFailure;

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

pub struct EntitySQLFetcher<'e, T = EntitySQLAttrConverterImpl<'e>, U = EntitySQLAncestorFetcherByAttr>
    where T: EntitySQLAttrConverter,
          U: EntitySQLAncestorFetcher
          {
    conn: &'e Connection,
    table_name: &'e str,
    id_attr_name: &'e str,
    attr_names: String,
    converter: T,
    ancestors: U
}

impl<'e, T: EntitySQLAttrConverter, U: EntitySQLAncestorFetcher> EntitySQLFetcher<'e, T, U> {
    pub fn new(conn: &'e Connection, table_name: &'e str, id_attr_name: &'e str, attr_names: &[&str], converter: T, ancestors: U) -> Self {
        let attr_names_string: String = attr_names.iter().map(|x| format!("\"{}\"", x)).collect::<Vec<String>>().join(", ");
        Self {
            conn,
            table_name,
            id_attr_name,
            attr_names: attr_names_string,
            converter,
            ancestors
        }
    }
}

impl<'a, T: EntitySQLAttrConverter> EntityFetcher for EntitySQLFetcher<'a, T> {
    fn get<'e>(&'e self, id: &EntityId) -> Option<(HashMap<String, PartialValue>, HashSet<EntityUid>)> {
        // TODO: escape attr names and table_name?
        let query = format!("SELECT {} FROM \"{}\" WHERE \"{}\" = ?", self.attr_names, self.table_name, self.id_attr_name);
         self.conn.query_row(&query,
            &[id.as_ref()], |row| Ok((self.converter.convert(row)?, self.ancestors.get_ancestors(id, self.conn, row)?)))
            .optional().expect("SQL query failed")  // TODO: if panic, return a result (maybe make return type Result<Option<...>>?)
    }
}

impl<'e> EntitySQLFetcher<'e> {
    pub fn simple(conn: &'e Connection, table_name: &'e str, attr_names: &[&'e str], ancestor_attr: &'e str) -> Self {
        let mut attr_names_with_ancestor: Vec<&'e str> = Vec::from(attr_names);
        attr_names_with_ancestor.push(ancestor_attr);
        EntitySQLFetcher::new(
            conn,
            table_name,
            "uid",
            &attr_names_with_ancestor,
            EntitySQLAttrConverterImpl::of_names(attr_names),
            EntitySQLAncestorFetcherByAttr::new(attr_names.len())
        )
    }
}

pub trait EntitySQLAttrConverter {
    // TODO: make our own error type?
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error>;
}

pub trait EntitySQLAncestorFetcher {
    fn get_ancestors(&self, id: &EntityId, conn: &Connection, query_result: &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error>;
}

pub struct EntitySQLAttrConverterImpl<'e> {
    // TODO: allow type checking?
    attr_names: Vec<(usize, &'e str)>,
}

pub struct EntitySQLAncestorFetcherByAttr {
    attr_index: usize
}

// TODO: Finish implementing this
pub struct EntitySQLAncestorFetcherByTable {
    query_string: String
}

#[allow(dead_code)]
impl EntitySQLAncestorFetcherByTable {
    fn new(table_name: &str, child_attr: &str, parent_attr: &str) -> Self {
        Self {
            query_string: format!("SELECT \"{}\" FROM \"{}\" WHERE \"{}\" = ?" , parent_attr, table_name, child_attr)
        }
    }
}

impl EntitySQLAncestorFetcherByAttr {
    fn new(attr_index: usize) -> Self {
        Self {
            attr_index
        }
    }
}

/// Should fetch ancestors based on a dedicated table for entities of this type
/// TODO: how should the table organize the different types of ancestors?
/// Or do we just make requests to all tables of ancestors?
#[allow(unused_mut, unused_variables)]
impl EntitySQLAncestorFetcher for EntitySQLAncestorFetcherByTable {
    fn get_ancestors(&self, id: &EntityId, conn: &Connection, _: &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error> {
        let mut stmt = conn.prepare(&self.query_string).unwrap();
        // stmt.query_and_then(&[id.as_ref()], |row| {
        //     todo!()
        // });
        todo!()
    }
}

impl EntitySQLAncestorFetcher for EntitySQLAncestorFetcherByAttr {
    fn get_ancestors(&self, _: &EntityId, _: &Connection, row: &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error> {
        serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(self.attr_index)?)
            .map_err(|e| FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e)))?
            .as_array().ok_or(rusqlite::Error::InvalidQuery)? // TODO: make an error type
            .iter()
            .map(|x| {
                EntityUid::from_json(x.clone()).map_err(|e| FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e)))
            })
            .collect()
    }
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
