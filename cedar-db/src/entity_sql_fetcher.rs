use std::{collections::{HashMap, HashSet}, borrow::Cow};

use cedar_policy::{EntityTypeName, PartialValue, EntityUid, EntityDatabase, ParsedEntity, Mode};
use rusqlite::{Connection, Row};


pub struct EntitySQLFetchTable {
    conn: Connection,
    table: HashMap<EntityTypeName, EntitySQLTypeFetcher>
}

pub struct EntitySQLTypeFetcher {
    table_name: &'static str,
    attr_names: Vec<&'static str>,
    converter: Box<dyn EntitySQLAttrConverter>,
}

pub trait EntitySQLAttrConverter {
    // TODO: make our own error type?
    fn convert(&self, query_result: &Row) -> Result<HashMap<String, PartialValue>, rusqlite::Error>;
}


impl EntityDatabase for EntitySQLFetchTable {
    fn get<'e>(&'e self, uid: &EntityUid) -> Option<Cow<'e, ParsedEntity>> {
        let type_fetcher = self.table.get(&uid.type_name())?;
        // TODO: escape attr names and table_name?
        let query = format!("SELECT \"{}\" FROM \"{}\" WHERE uid = ?",
            type_fetcher.attr_names
            .iter()
            .map(|x| format!("\"{}\"", x))
            .collect::<Vec<String>>()
            .join(", "), type_fetcher.table_name);
        let result: Result<HashMap<String, PartialValue>, _> = self.conn.query_row(&query,
            &[uid.id().as_ref()], |row| type_fetcher.converter.convert(row));
        result.ok().map(|attrs| Cow::Owned(ParsedEntity::new(uid.clone(), attrs, HashSet::new())))
    }

    fn partial_mode(&self) -> Mode {
        Mode::Partial
    }
}
