use std::{collections::HashMap, str::FromStr};

use cedar_policy::{EntityTypeName, EntityDatabase, EntityUid, Authorizer, Request, Context};
use entity_sql_fetcher::EntitySQLFetchTable;
use rusqlite::Connection;
use lazy_static::lazy_static;

use crate::entity_sql_fetcher::*;

mod entity_sql_fetcher;

lazy_static! {

    static ref ENTITY_TABLE: HashMap<EntityTypeName, EntitySQLTypeFetcher> = {
        // let users_entity_parser: EntitySQLAttrConverterImpl = {
        //     EntitySQLAttrConverterImpl::new(vec![
        //         (0, "name"),
        //         (1, "age")
        //     ])
        // };

        let mut table = HashMap::new();
        // table.insert(EntityTypeName::from_str("Users").unwrap(), EntitySQLTypeFetcher::new("users", vec!["name", "age"], Box::new(users_entity_parser)));
        table.insert(EntityTypeName::from_str("Users").unwrap(), EntitySQLTypeFetcher::new_default("users", vec!["name", "age"]));
        table
    };
}

fn main() {
    let conn = Connection::open("cedar-db/example.db").expect("Connection failed");
    let table: EntitySQLFetchTable = EntitySQLFetchTable::new(conn, &ENTITY_TABLE);
    let result = table.get(&"Users::\"0\"".parse().unwrap());
    println!("{:?}", result);

    // let auth = Authorizer::new();
    // let result = auth.is_authorized_parsed(
    //     &Request::new(Some("Users::\"0\"".parse().unwrap()),
    //         Some("Actions::\"view\"".parse().unwrap()),
    //         Some("Photos::\"20\"".parse().unwrap()), Context::empty())
    //     , &"permit(principal, action, resource) when { principal.age == 20 };".parse().unwrap(),
    //     &table);
    // println!("Result {}", result);
}
