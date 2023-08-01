use std::collections::{HashMap, HashSet};

use cedar_policy::{PartialValue, EntityUid, ParsedEntity, EntityId, EntityTypeName};
use ref_cast::RefCast;
use rusqlite::{Connection, Row, OptionalExtension, types::{FromSql, ValueRef}, Error};
use rusqlite::Error::FromSqlConversionFailure;


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

    pub fn get_ancestors(&self, conn: &Connection, id: &EntityId, tp: &EntityTypeName) -> HashSet<EntityUid> {
        // println!("Running query {} with params {}", self.query_string, id.as_ref());
        let mut stmt = conn.prepare(&self.query_string).expect("Failed to prepare statement");
        stmt.query_map(&[id.as_ref()], |row| -> Result<EntityUid, Error> {
            let parent_id: EntitySQLId = row.get(0)?;
            Ok(EntityUid::from_type_name_and_id(tp.clone(), parent_id.0))
        })
        .expect("Failed to query")
        .collect::<Result<HashSet<EntityUid>, Error>>()
        .expect("Failed to parse rows")
    }
}

pub fn convert_attr_names(query_result: &Row, attr_names: &[(usize, &str)]) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
    attr_names.iter()
        .filter_map(|(ind, nm)| {
            match query_result.get::<_, SQLPartialValue>(*ind) {
                Ok(SQLPartialValue(Some(v))) => Some(Ok((nm.to_string(), v))),
                Ok(SQLPartialValue(None)) => None,
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


/*
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

impl<'a, T: EntitySQLAttrConverter, U: EntitySQLAncestorFetcher> EntityFetcher for EntitySQLFetcher<'a, T, U> {
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

pub struct DynamicSQLAttrConverter {
    convert: Box<dyn Fn(&Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error>>
}

impl DynamicSQLAttrConverter {
    pub fn new(convert: impl Fn(&Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error> + 'static) -> Self {
        Self { convert: Box::new(convert) }
    }
}

impl EntitySQLAttrConverter for DynamicSQLAttrConverter {
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
        (self.convert)(query_result)
    }
}

pub struct DynamicSQLAncestorFetcher {
    get_ancestors: Box<dyn Fn(&EntityId, &Connection, &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error>>
}

impl DynamicSQLAncestorFetcher {
    pub fn new(get_ancestors: impl Fn(&EntityId, &Connection, &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error> + 'static) -> Self {
        Self { get_ancestors: Box::new(get_ancestors) }
    }
}

impl EntitySQLAncestorFetcher for DynamicSQLAncestorFetcher {
    fn get_ancestors(&self, id: &EntityId, conn: &Connection, query_result: &Row<'_>) -> Result<HashSet<EntityUid>, rusqlite::Error> {
        (self.get_ancestors)(id, conn, query_result)
    }
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

    pub fn convert_attr_names(attr_names: &[(usize, &str)], query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
        attr_names.iter()
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

impl<'e> EntitySQLAttrConverter for EntitySQLAttrConverterImpl<'e> {

    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error> {
        EntitySQLAttrConverterImpl::convert_attr_names(&self.attr_names, query_result)
    }
}
*/