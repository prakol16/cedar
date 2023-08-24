#[cfg(feature = "rusqlite")]
pub mod sqlite;

#[cfg(feature = "postgres")]
pub mod postgres;

pub mod query_expr;
pub mod query_expr_iterator;
pub mod expr_to_query;
pub mod query_builder;

#[cfg(feature = "postgres")]
#[cfg(test)]
mod test_postgres {
    use std::{borrow::Cow, collections::HashMap};

    use cedar_policy::{EntityUid, EntityTypeName, Authorizer, Request, Context, EntityDatabase, EntityAttrDatabase, PartialValue, EntityAttrAccessError, CachedEntities, Decision};
    use postgres::{Client, NoTls};

    use crate::postgres::*;

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "host=localhost user=postgres dbname=example_postgres password=postgres";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();
        static ref ASSIGNMENTS_TYPE: EntityTypeName = "Assignments".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));
        static ref ASSIGNMENTS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("assignments", vec!["tasks", "owner"], None);

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
                t if *t == *ASSIGNMENTS_TYPE =>
                    Ok(conn.query_opt(ASSIGNMENTS_TABLE_INFO.get_query_string(), &[&uid.id().as_ref()])?
                        .map(|row| convert_attr_names(&row, &ASSIGNMENTS_TABLE_INFO.attr_names))
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
        let result = auth.is_authorized_full_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Photos::\"2\"".parse().unwrap()), Context::empty())
            , &"permit(principal, action, resource) when { principal.name == \"Bob\" && principal in Teams::\"0\" };".parse().unwrap(),
            &table);
        assert!(result.decision() == Decision::Allow);
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

        let result = auth.is_authorized_full_parsed(
            &request,
              &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
            &CachedEntities::cache_request(&Table, &request));

        assert!(result.decision() == Decision::Allow);
    }

    #[test]
    fn test_json_deserialize() {
        let table = make_entity_attr_database();
        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"1\"".parse().unwrap();
        let result1 = auth.is_authorized_full_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Assignments::\"0\"".parse().unwrap()), Context::empty())
            , &r#"permit(principal, action, resource) when { principal == resource.owner };"#.parse().unwrap(),
            &table);
        assert!(result1.decision() == Decision::Deny);

        let result2 = auth.is_authorized_full_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Assignments::\"0\"".parse().unwrap()), Context::empty())
            , &r#"permit(principal, action, resource) when { principal == resource.owner || (resource.tasks has "task0" && !resource.tasks.task0.completed) };"#.parse().unwrap(),
            &table);
        assert!(result2.decision() == Decision::Allow);
    }
}

#[cfg(feature = "rusqlite")]
#[cfg(test)]
mod test_sqlite {
    use std::borrow::Cow;

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName, Schema, Decision, PartialResponse, RestrictedExpression, PolicySet};

    use cedar_policy_core::{ast::Expr, entities::SchemaType};
    use rusqlite::Connection;
    use sea_query::{Alias, SqliteQueryBuilder};

    use crate::{sqlite::*, expr_to_query::{InByTable, InByLambda}, query_builder::{translate_response, translate_expr}};

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "test/example_sqlite.db";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<'static> = AncestorSQLInfo::new("team_memberships", "user", "team");
    }

    fn get_conn() -> Connection {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");
        conn.pragma_update(None, "case_sensitive_like", true).expect("Failed to set case_sensitive_like");
        conn
    }

    fn get_sqlite_table() -> impl EntityDatabase {
        let conn = get_conn();
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
    fn test_like() {
        let e: Expr = r#""test _%\\randomstuff*" like "test _%\\*\*""#.parse().unwrap();
        let mut q = translate_expr(&e, &get_schema(),
        InByLambda {
            ein: |_, _, _, _| panic!("should not be building 'in' statement"),
            ein_set: |_, _, _, _| panic!("should not be building 'in' statement")
        }, |_| (Alias::new(""), Alias::new(""))).expect("Failed to translate expression")
        .into_select_statement();
        q.expr(true);
        assert_eq!(q.to_string(SqliteQueryBuilder), r#"SELECT TRUE WHERE 'test _%\randomstuff*' LIKE 'test \_\%\\%*' ESCAPE '\'"#);
    }

    #[test]
    fn test_partial_eval_row_filter() {
        let auth = Authorizer::new();

        let q = Request::builder()
            .principal(Some("Users::\"1\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource(Some("Photos::\"2\"".parse().unwrap()))
            .context(Context::from_pairs([
                ("age".into(), RestrictedExpression::new_unknown("age", Some(SchemaType::Long)))
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
                        InByTable::<Alias, Alias, _>(|_, _| {
                            panic!("There should not be any in's in the residual")
                        }), |_| {
                            panic!("There should not be any tables in the residual")
                        }).expect("Failed to translate response");
                    let query =  query.into_select_statement()
                        .column(sea_query::Asterisk)
                        .from(Alias::new("people"))
                        .to_string(SqliteQueryBuilder);
                    assert_eq!(query, r#"SELECT * FROM "people" WHERE TRUE AND (TRUE AND 20 <= "age" AND "age" <= 30) AND TRUE"#);
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
                    InByTable::<Alias, Alias, _>(|_, _| {
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
                query.query_default_attr("title").expect("Query should have exactly one unknown");
                let query =  query.to_string_sqlite();
                assert_eq!(query, r#"SELECT "resource"."title" FROM "photos" AS "resource" LEFT JOIN "users" AS "temp__0" ON "resource"."user_id" = "temp__0"."uid" WHERE TRUE AND (TRUE AND "temp__0"."name" = 'Alice') AND TRUE"#);

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

#[cfg(feature = "rusqlite")]
#[cfg(test)]
mod test_docs_example {
    use std::borrow::Cow;

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName, Schema, Decision, PartialResponse, RestrictedExpression, PolicySet};

    use cedar_policy_core::{ast::Expr, entities::SchemaType};
    use rusqlite::Connection;
    use sea_query::{Alias, SqliteQueryBuilder};

    use crate::{sqlite::*, expr_to_query::{InByTable, InByLambda}, query_builder::{translate_response, translate_expr}};


    fn get_schema() -> Schema {
        // schema:
        // There are users, documents, and teams.
        // Users each have a string "role"
        // Documents each have a string "title" and a user "owner"
        // Teams have a string "name"
        // Users can be children of teams
        r#"
        {
            "": {
                "entityTypes": {
                    "Users": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "role": {
                                    "type": "String"
                                }
                            }
                        },
                        "memberOfTypes": ["Teams"]
                    },
                    "Documents": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "title": {
                                    "type": "String"
                                },
                                "owner": {
                                    "type": "Entity",
                                    "name": "Users"
                                }
                            }
                        }
                    },
                    "Teams": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "name": {
                                    "type": "String"
                                }
                            }
                        }
                    }
                },
                "actions": {
                    "view": {
                        "appliesTo": {
                            "principalTypes": ["Users"],
                            "resourceTypes": ["Documents"]
                        }
                    }
                }
            }
        }
        "#.parse().expect("Document schema should parse correctly")
    }


    fn get_policies_docs_example() -> PolicySet {
        r#"
        // Any vp can see any documents made by interns
        permit(principal, action, resource) when {
            principal.role == "vp" && resource.owner.role == "intern";
        };

        // The document with id 'doc4' is shared with everyone in Cedar
        permit(principal in Teams::"cedar", action, resource == Documents::"doc4");
        "#.parse().unwrap()
    }


    #[test]
    fn test_partial_eval_docs_example() {
        let schema = get_schema();
        let pset = get_policies_docs_example();

        let auth = Authorizer::new();
        let q: Request = Request::builder()
            .principal(Some("Users::\"danielle\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource(Some("Documents::\"doc4\"".parse().unwrap()))
            .build();


    }
}