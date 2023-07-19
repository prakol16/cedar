use std::collections::HashMap;

use cedar_policy::{EntityTypeName, RestrictedExpression};


pub struct EntityFetchTable(HashMap<EntityTypeName, EntityTypeFetcher>);

pub struct EntityTypeFetcher {
    table_name: &'static str,
    attr_names: Vec<&'static str>,
    converter: Box<dyn EntityAttrConverter>,
}

pub trait EntityAttrConverter {
    fn convert(&self, query_result: &rusqlite::Row) -> HashMap<String, RestrictedExpression>;
}


