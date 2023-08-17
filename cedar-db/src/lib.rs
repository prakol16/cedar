#[cfg(feature = "rusqlite")]
pub mod sqlite;

#[cfg(feature = "postgres")]
pub mod postgres;

pub mod query_expr;
pub mod expr_to_query;

#[cfg(feature = "postgres")]
#[cfg(test)]
mod test_postgres {
    use std::{borrow::Cow, collections::HashMap};

    use cedar_policy::{EntityUid, EntityTypeName, Authorizer, Request, Context, EntityDatabase, EntityAttrDatabase, PartialValue, EntityAttrAccessError, CachedEntities};
    use postgres::{Client, NoTls};

    use crate::postgres::*;

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "host=localhost user=postgres dbname=example_postgres password=postgres";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<'static> = AncestorSQLInfo::new("team_memberships", "user_id", "team_id");
    }


    #[test]
    fn test_basic() {
        let mut conn = Client::connect(&*DB_PATH, NoTls)
            .expect("Connection failed");

        let euid: EntityUid = "Users::\"0\"".parse().unwrap();

        let entity = USERS_TABLE_INFO.make_entity_ancestors(&mut conn, &euid)
            .expect("Failed to make entity");
        println!("Result: {:?}", entity); // should be Users::"0" named "Alice" with parent Users::"1"
    }

    fn make_entity_attr_database() -> impl EntityAttrDatabase {
        struct Table;

        fn get_entity_attrs(uid: &EntityUid) -> Result<Option<HashMap<String, PartialValue>>, PostgresToCedarError> {
            let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
            match uid.type_name() {
                t if *t == *USERS_TYPE =>
                    Ok(conn.query_opt(USERS_TABLE_INFO.get_query_string(), &[&uid.id().as_ref()])?
                        .map(|row| convert_attr_names(&row, &USERS_TABLE_INFO.attr_names))
                        .transpose()?),
                t if *t == *PHOTOS_TYPE =>
                    Ok(conn.query_opt(PHOTOS_TABLE_INFO.get_query_string(), &[&uid.id().as_ref()])?
                        .map(|row| convert_attr_names(&row, &PHOTOS_TABLE_INFO.attr_names))
                        .transpose()?),
                _ => Ok(None)
            }
        }

        impl EntityAttrDatabase for Table {
            type Error = PostgresToCedarError;

            fn exists_entity(&self, uid: &EntityUid) -> Result<bool, Self::Error> {
                Ok(get_entity_attrs(uid)?.is_some())
            }

            fn entity_attr<'e>(&'e self, uid: &EntityUid, attr: &str) -> Result<PartialValue, EntityAttrAccessError<Self::Error>> {
                get_entity_attrs(uid)?
                .ok_or(EntityAttrAccessError::UnknownEntity)
                .and_then(|attrs| attrs.get(attr).cloned().ok_or(EntityAttrAccessError::UnknownAttr))
            }

            fn entity_in(&self, u1: &EntityUid, u2: &EntityUid) -> Result<bool, Self::Error> {
                match (u1.type_name(), u2.type_name()) {
                    (t1, t2) if *t1 == *USERS_TYPE && *t2 == *TEAMS_TYPE => {
                        let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                        USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&mut conn, u1.id(), u2.id())
                    },
                    _ => Ok(false)
                }
            }

            fn partial_mode(&self) -> cedar_policy::Mode {
                cedar_policy::Mode::Concrete
            }
        }

        Table
    }

    #[test]
    fn test_entity_attr_database() {
        let table = make_entity_attr_database();
        assert!(table.entity_in(&"Users::\"1\"".parse().unwrap(), &"Teams::\"0\"".parse().unwrap()).expect("Failed to check entity in"));
        assert!(!table.entity_in(&"Users::\"0\"".parse().unwrap(), &"Teams::\"0\"".parse().unwrap()).expect("Failed to check entity in"));
    }

    #[test]
    fn test_auth_entity_attr_database() {
        let table = make_entity_attr_database();
        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"1\"".parse().unwrap();
        let result = auth.is_authorized_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Photos::\"2\"".parse().unwrap()), Context::empty())
            , &"permit(principal, action, resource) when { principal.name == \"Bob\" && principal in Teams::\"0\" };".parse().unwrap(),
            &table);
        println!("Result: {:?}", result);
    }

    #[test]
    fn test_auth() {
        struct Table;

        impl EntityDatabase for Table {
            type Error = PostgresToCedarError;

            fn get<'e>(&'e self, uid: &EntityUid) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, Self::Error> {
                let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO.make_entity_ancestors(&mut conn, uid)?.map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO.make_entity_ancestors(&mut conn, uid)?.map(Cow::Owned)),
                    _ => Ok(None)
                }
            }

            fn partial_mode(&self) -> cedar_policy::Mode {
                cedar_policy::Mode::Concrete
            }
        }

        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"0\"".parse().unwrap();
        let request = Request::new(Some(euid.clone()),
            Some("Actions::\"view\"".parse().unwrap()),
            Some("Photos::\"2\"".parse().unwrap()), Context::empty());

        let result = auth.is_authorized_parsed(
            &request,
              &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
            &CachedEntities::cache_request(&Table, &request));

        println!("Result {:?}", result);  // should be allow
    }
}

#[cfg(feature = "rusqlite")]
#[cfg(test)]
mod test_sqlite {
    use std::borrow::Cow;

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName, Schema, Decision, PartialResponse, RestrictedExpression};

    use cedar_policy_core::ast::Type;
    use rusqlite::Connection;
    use sea_query::{Alias, SqliteQueryBuilder, SimpleExpr, Query};

    use crate::{sqlite::*, expr_to_query::{translate_response, InByTable}};

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "test/example_sqlite.db";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<'static> = AncestorSQLInfo::new("team_memberships", "user", "team");
    }

    fn get_sqlite_table() -> impl EntityDatabase {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");
        struct Table { conn: Connection }

        impl EntityDatabase for Table {
            type Error = rusqlite::Error;

            fn get<'e>(&'e self, uid: &EntityUid) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, Self::Error> {
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO.make_entity_ancestors(&self.conn, uid)?.map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO.make_entity_ancestors(&self.conn, uid)?.map(Cow::Owned)),
                    _ => Ok(None)
                }
            }

            fn partial_mode(&self) -> cedar_policy::Mode {
                cedar_policy::Mode::Concrete
            }
        }

        Table { conn }
    }

    fn get_schema() -> Schema {
        r#"
        {
            "": {
                "entityTypes": {
                    "Users": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "name": {
                                    "type": "String"
                                },
                                "age": {
                                    "type": "Long"
                                },
                                "location": {
                                    "type": "String",
                                    "required": false
                                }
                            }
                        }
                    },
                    "Photos": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "title": {
                                    "type": "String"
                                },
                                "user_id": {
                                    "type": "Entity",
                                    "name": "Users"
                                }
                            }
                        }
                    }
                },
                "actions": {
                    "view": {
                        "appliesTo": {
                            "principalTypes": ["Users"],
                            "resourceTypes": ["Photos"]
                        }
                    }
                }
            }
        }
        "#.parse().expect("Schema should not fail to parse")
    }

    #[test]
    fn test_sea_query() {
        let e = SimpleExpr::from(true).and(SimpleExpr::from(true).and(SimpleExpr::from(20).eq(20)).and(SimpleExpr::from(30).eq(30)));
        println!("Expr: {}",  Query::select().and_where(e).to_string(SqliteQueryBuilder));
    }

    #[test]
    fn test_sea_query2() {
        let e = SimpleExpr::from(true).and(SimpleExpr::from(true).and(true.into()).and(true.into()));
        println!("Expr: {}",  Query::select().and_where(e).to_string(SqliteQueryBuilder));
    }

    #[test]
    fn test_partial_eval_row_filter() {
        let auth = Authorizer::new();

        let q = Request::builder()
            .principal(Some("Users::\"1\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource(Some("Photos::\"2\"".parse().unwrap()))
            .context(Context::from_pairs([
                ("age".into(), RestrictedExpression::new_unknown("age", Some(Type::Long)))
            ]))
            .build();


        let result = auth.is_authorized_parsed(&q,
            // Only 20-30 year olds can see photo 2
            &"permit(principal, action, resource) when { resource == Photos::\"2\" && 20 <= context.age && context.age <= 30 };".parse().unwrap(),
            &get_sqlite_table());

            match result {
                PartialResponse::Concrete(_) => panic!("Response should be residual"),
                PartialResponse::Residual(res) => {
                    #[allow(unused_mut)]
                    let mut query = translate_response::<Alias, Alias>(&res, &get_schema(),
                        &InByTable::<Alias, Alias, _>(|_, _| {
                            panic!("There should not be any in's in the residual")
                        }), |_| {
                            panic!("There should not be any tables in the residual")
                        }).expect("Failed to translate response");
                    println!("Query: {:?}", query);
                    // This actually illustrates a bug in sea-query
                    // let query =  query
                    //     .column(Asterisk)
                    //     .from(Alias::new("people"))
                    //     .to_string(SqliteQueryBuilder);
                    // println!("Query: {}", query);
                }
            }

    }

    #[test]
    fn test_partial_eval_nested_attr() {
        let schema = get_schema();

        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"1\"".parse().unwrap();

        let q = Request::builder()
            .principal(Some(euid.clone()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource_type("Photos".parse().unwrap())
            .build();

        let result = auth.is_authorized_parsed(&q,
            // Bob can see Alice's photos
            &"permit(principal, action, resource) when { principal.name == \"Bob\" && resource.user_id.name == \"Alice\" };".parse().unwrap(),
            &get_sqlite_table());
        match result {
            PartialResponse::Concrete(_) => panic!("Response should be residual"),
            PartialResponse::Residual(res) => {
                let mut query = translate_response(&res, &schema,
                    &InByTable::<Alias, Alias, _>(|_, _| {
                        panic!("There should not be any in's in the residual")
                    }), |tp| {
                        (if *tp == *USERS_TYPE {
                            Alias::new(USERS_TABLE_INFO.table)
                        } else if *tp == *PHOTOS_TYPE {
                            Alias::new(PHOTOS_TABLE_INFO.table)
                        } else {
                            panic!("Unknown type")
                        }, Alias::new("uid"))
                    }).expect("Failed to translate response");
                let query =  query
                    .column((Alias::new("resource"), Alias::new("title")))
                    .from_as(Alias::new("photos"), Alias::new("resource"))
                    .to_string(SqliteQueryBuilder);
                assert_eq!(query, r#"SELECT "resource"."title" FROM "photos" AS "resource" INNER JOIN "users" AS "v__entity_attr_0" ON "resource"."user_id" = "v__entity_attr_0"."uid" WHERE TRUE AND (TRUE AND ("v__entity_attr_0"."name" = 'Alice')) AND TRUE"#);

                let conn = Connection::open(&*DB_PATH).expect("Connection failed");
                conn.query_row(&query, [], |row| {
                    assert_eq!(row.get::<_, String>(0).expect("Row should have title column"), "Beach photo");
                    Ok(())
                }).expect("Failed to query");
            },
        }
    }

    #[test]
    fn test_ancestors() {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");

        println!("Ancestors: {:?}", USERS_TEAMS_MEMBERSHIP_INFO.get_ancestors(&conn, &"1".parse().unwrap(), &TEAMS_TYPE));

        assert!(USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&conn, &"1".parse().unwrap(), &"0".parse().unwrap()).expect("Failed to check ancestor"));

        assert!(!USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&conn, &"0".parse().unwrap(), &"1".parse().unwrap()).expect("Failed to check ancestor"));
    }

    #[test]
    fn test_basic() {
        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"0\"".parse().unwrap();
        let result = auth.is_authorized_full_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Photos::\"2\"".parse().unwrap()), Context::empty())
            , &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
            &get_sqlite_table());
        assert!(result.decision() == Decision::Allow);
    }

}