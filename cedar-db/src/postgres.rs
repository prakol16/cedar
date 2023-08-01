use std::collections::HashMap;

use cedar_policy::Value;
use postgres::{Client, NoTls, types::{FromSql, Type, Kind}};
use ref_cast::RefCast;

#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
struct SQLValue(Option<Value>);

impl<T: Into<Value>> From<T> for SQLValue {
    fn from(v: T) -> Self {
        SQLValue(Some(v.into()))
    }
}

impl<'a> FromSql<'a> for SQLValue {
    fn from_sql(ty: &Type, raw: &'a [u8]) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        if bool::accepts(ty) {
            Ok(bool::from_sql(ty, raw)?.into())
        } else if i32::accepts(ty) {
            Ok((i32::from_sql(ty, raw)? as i64).into())
        } else if i64::accepts(ty) {
            Ok(i64::from_sql(ty, raw)?.into())
        } else if u32::accepts(ty) {
            Ok((u32::from_sql(ty, raw)? as i64).into())
        } else if String::accepts(ty) {
            Ok(String::from_sql(ty, raw)?.into())
        } else if <HashMap<String, Option<String>> as FromSql>::accepts(ty) {
            Ok(<HashMap<String, Option<String>> as FromSql>::from_sql(ty, raw)?
            .into_iter()
            .filter_map(|(k, v)| Some((k, v?.into())))
            .collect::<Vec<(String, Value)>>()
            .into())
        } else if let Kind::Array(inner) = ty.kind() {
            Ok(<Vec<SQLValue> as FromSql>::from_sql(inner, raw)?
                .into_iter()
                .filter_map(|v| v.0)
                .collect::<Vec<Value>>()
                .into())
        } // TODO: support json/jsonb formats using serde_json
        else {
            Err(format!("unsupported type: {:?}", ty).into())
        }
    }

    fn from_sql_null(_ : &Type) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        Ok(SQLValue(None))
    }

    fn accepts(ty: &postgres::types::Type) -> bool {
        bool::accepts(ty) ||
        i32::accepts(ty) ||
        i64::accepts(ty) ||
        u32::accepts(ty) ||
        String::accepts(ty) ||
        <HashMap<String, Option<String>> as FromSql>::accepts(ty) ||
        (match ty.kind() {
            Kind::Array(inner) => <SQLValue as FromSql>::accepts(inner),
            _ => false
        })
    }
}

pub fn do_random_stuff() {
    let mut client = Client::connect("host=localhost user=postgres dbname=example_postgres password=postgres", NoTls)
        .expect("Connection failed");
    let rows = client.query("SELECT * FROM users", &[]).expect("query failed");
    for row in rows {
        let id: i32 = row.get(0);
        let name: &str = row.get(1);
        println!("found person: {} {}", id, name);
    }
}
