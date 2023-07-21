use std::{collections::HashMap, str::FromStr};

use cedar_policy::{EntityTypeName, EntityDatabase, EntityUid, Authorizer, Request, Context};
use entity_sql_fetcher::EntitySQLFetchTable;
use rusqlite::Connection;
use lazy_static::lazy_static;

use crate::entity_sql_fetcher::*;

mod entity_sql_fetcher;

lazy_static! {

    static ref ENTITY_TABLE: HashMap<EntityTypeName, EntitySQLTypeFetcher> = {
        HashMap::from([
            ("Users".parse().unwrap(), EntitySQLTypeFetcher::new_default("users", &["name", "age"])),
            ("Photos".parse().unwrap(), EntitySQLTypeFetcher::new_default("photos", &["title", "location"]))
        ])
    };
}

fn main() {
    let conn = Connection::open("cedar-db/example.db").expect("Connection failed");
    let table: EntitySQLFetchTable = EntitySQLFetchTable::new(conn, &ENTITY_TABLE);

    let auth = Authorizer::new();
    let result = auth.is_authorized_parsed(
        &Request::new(Some("Users::\"0\"".parse().unwrap()),
            Some("Actions::\"view\"".parse().unwrap()),
            Some("Photos::\"20\"".parse().unwrap()), Context::empty())
        , &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
        &table);
    println!("Result {:?}", result);
}
