/*
 * Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Integration between SQL databases and Cedar entity stores
#![forbid(unsafe_code)]
#![warn(missing_docs, missing_debug_implementations, rust_2018_idioms)]

pub mod sea_query_extra;
pub mod sql_common;

#[cfg(feature = "rusqlite")]
pub mod sqlite;

#[cfg(feature = "postgres")]
pub mod postgres;

pub mod dump_entities;

pub mod expr_to_query;
pub mod query_builder;
pub mod query_expr;
pub mod query_expr_iterator;

#[cfg(test)]
mod idens {
    #[derive(sea_query::Iden)]
    pub(crate) enum Idens {
        Users,
        Ancestors,
        Photos,
        Assignments,
        Owner,
        TeamMemberships,
        UserId,
        TeamId,
        User,
        Team,
        UsersInTeams,
        UserUid,
        TeamUid,
        Docs,
        Teams,
    }
}

#[cfg(feature = "postgres")]
#[cfg(test)]
mod test_postgres {
    use std::borrow::Cow;

    use cedar_policy::{
        Authorizer, CachedEntities, Context, Decision, EntityAttrAccessError, EntityAttrDatabase,
        EntityDatabase, EntityTypeName, EntityUid, PartialValue, Request,
    };
    use postgres::{Client, NoTls};

    use crate::{
        idens::Idens,
        postgres::*,
        sql_common::{AncestorSQLInfo, DatabaseToCedarError, EntitySQLInfo},
    };

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "host=localhost user=postgres dbname=example_postgres password=postgres";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();
        static ref ASSIGNMENTS_TYPE: EntityTypeName = "Assignments".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<PostgresSQLInfo> = EntitySQLInfo::simple(Idens::Users, vec!["name".into(), "age".into()], Some(Idens::Ancestors));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<PostgresSQLInfo> = EntitySQLInfo::simple(Idens::Photos, vec!["title", "location"], Some(Idens::Ancestors));
        static ref ASSIGNMENTS_TABLE_INFO: EntitySQLInfo<PostgresSQLInfo> = EntitySQLInfo::simple(Idens::Assignments, vec!["tasks", "owner"], Some(Idens::Owner));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<PostgresSQLInfo> = AncestorSQLInfo::new(Idens::TeamMemberships, Idens::UserId, Idens::TeamId);
    }

    #[test]
    fn test_basic() {
        let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");

        let euid: EntityUid = "Users::\"0\"".parse().unwrap();

        let entity = USERS_TABLE_INFO
            .make_entity_ancestors(&mut conn, &euid)
            .expect("Failed to make entity");
        println!("Result: {:?}", entity); // should be Users::"0" named "Alice" with parent Users::"1"
    }

    fn make_entity_attr_database() -> impl EntityAttrDatabase {
        struct Table;

        impl EntityAttrDatabase for Table {
            type Error = DatabaseToCedarError;

            fn exists_entity(&self, uid: &EntityUid) -> Result<bool, Self::Error> {
                let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                match uid.type_name() {
                    t if *t == *USERS_TYPE => {
                        Ok(USERS_TABLE_INFO.exists_entity(&mut conn, uid.id())?)
                    }
                    t if *t == *PHOTOS_TYPE => {
                        Ok(PHOTOS_TABLE_INFO.exists_entity(&mut conn, uid.id())?)
                    }
                    t if *t == *ASSIGNMENTS_TYPE => {
                        Ok(ASSIGNMENTS_TABLE_INFO.exists_entity(&mut conn, uid.id())?)
                    }
                    _ => Ok(false),
                }
            }

            fn entity_attr<'e>(
                &'e self,
                uid: &EntityUid,
                attr: &str,
            ) -> Result<PartialValue, EntityAttrAccessError<Self::Error>> {
                let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO
                        .get_single_attr(&mut conn, uid.id(), attr)?
                        .into()),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO
                        .get_single_attr(&mut conn, uid.id(), attr)?
                        .into()),
                    t if *t == *ASSIGNMENTS_TYPE => Ok(ASSIGNMENTS_TABLE_INFO
                        .get_single_attr(&mut conn, uid.id(), attr)?
                        .into()),
                    _ => Err(EntityAttrAccessError::UnknownEntity),
                }
            }

            fn entity_in(&self, u1: &EntityUid, u2: &EntityUid) -> Result<bool, Self::Error> {
                match (u1.type_name(), u2.type_name()) {
                    (t1, t2) if *t1 == *USERS_TYPE && *t2 == *TEAMS_TYPE => {
                        let mut conn =
                            Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                        USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&mut conn, u1.id(), u2.id())
                    }
                    _ => Ok(false),
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
        assert!(table
            .entity_in(
                &"Users::\"1\"".parse().unwrap(),
                &"Teams::\"0\"".parse().unwrap()
            )
            .expect("Failed to check entity in"));
        assert!(!table
            .entity_in(
                &"Users::\"0\"".parse().unwrap(),
                &"Teams::\"0\"".parse().unwrap()
            )
            .expect("Failed to check entity in"));
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
            type Error = DatabaseToCedarError;

            fn get<'e>(
                &'e self,
                uid: &EntityUid,
            ) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, Self::Error>
            {
                let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO
                        .make_entity_ancestors(&mut conn, uid)?
                        .map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO
                        .make_entity_ancestors(&mut conn, uid)?
                        .map(Cow::Owned)),
                    _ => Ok(None),
                }
            }

            fn partial_mode(&self) -> cedar_policy::Mode {
                cedar_policy::Mode::Concrete
            }
        }

        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"0\"".parse().unwrap();
        let request = Request::new(
            Some(euid.clone()),
            Some("Actions::\"view\"".parse().unwrap()),
            Some("Photos::\"2\"".parse().unwrap()),
            Context::empty(),
        );

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
            &Request::new(
                Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Assignments::\"0\"".parse().unwrap()),
                Context::empty(),
            ),
            &r#"permit(principal, action, resource) when { principal == resource.owner };"#
                .parse()
                .unwrap(),
            &table,
        );
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

    use cedar_policy::{
        Authorizer, Context, Decision, EntityDatabase, EntityTypeName, EntityUid, PartialResponse,
        Request, RestrictedExpression, Schema,
    };

    use cedar_policy_core::{ast::Expr, entities::SchemaType};
    use rusqlite::Connection;
    use sea_query::{Alias, SqliteQueryBuilder};

    use crate::{
        expr_to_query::{InByLambda, InByTable},
        query_builder::{translate_expr, translate_response},
        {
            idens::Idens,
            sql_common::{AncestorSQLInfo, DatabaseToCedarError, EntitySQLInfo},
            sqlite::*,
        },
    };

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "test/example_sqlite.db";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<SQLiteSQLInfo> = EntitySQLInfo::simple(Idens::Users, vec!["name", "age"], Some(Idens::Ancestors));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<SQLiteSQLInfo> = EntitySQLInfo::simple(Idens::Photos, vec!["title", "location"], Some(Idens::Ancestors));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<SQLiteSQLInfo> = AncestorSQLInfo::new(Idens::TeamMemberships, Idens::User, Idens::Team);
    }

    fn get_conn() -> Connection {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");
        conn.pragma_update(None, "case_sensitive_like", true)
            .expect("Failed to set case_sensitive_like");
        conn
    }

    fn get_sqlite_table() -> impl EntityDatabase {
        let conn = get_conn();
        struct Table {
            conn: Connection,
        }

        impl EntityDatabase for Table {
            type Error = DatabaseToCedarError;

            fn get<'e>(
                &'e self,
                uid: &EntityUid,
            ) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, Self::Error>
            {
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO
                        .make_entity_ancestors(&self.conn, uid)?
                        .map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO
                        .make_entity_ancestors(&self.conn, uid)?
                        .map(Cow::Owned)),
                    _ => Ok(None),
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
        "#
        .parse()
        .expect("Schema should not fail to parse")
    }

    #[test]
    fn test_like() {
        let e: Expr = r#""test _%\\randomstuff*" like "test _%\\*\*""#.parse().unwrap();
        let mut q = translate_expr(
            &e,
            &get_schema(),
            InByLambda {
                ein: |_, _, _, _| panic!("should not be building 'in' statement"),
                ein_set: |_, _, _, _| panic!("should not be building 'in' statement"),
            },
            |_| (Alias::new(""), "".into()),
        )
        .expect("Failed to translate expression")
        .into_select_statement();
        q.expr(true);
        assert_eq!(
            q.to_string(SqliteQueryBuilder),
            r#"SELECT TRUE WHERE 'test _%\randomstuff*' LIKE 'test \_\%\\%*' ESCAPE '\'"#
        );
    }

    #[test]
    fn test_partial_eval_row_filter() {
        let auth = Authorizer::new();

        let q = Request::builder()
            .principal(Some("Users::\"1\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource(Some("Photos::\"2\"".parse().unwrap()))
            .context(Context::from_pairs([(
                "age".into(),
                RestrictedExpression::new_unknown("age", Some(SchemaType::Long)),
            )]))
            .build();

        let result = auth.is_authorized_parsed(&q,
            // Only 20-30 year olds can see photo 2
            &"permit(principal, action, resource) when { resource == Photos::\"2\" && 20 <= context.age && context.age <= 30 };".parse().unwrap(),
            &get_sqlite_table());

        match result {
            PartialResponse::Concrete(_) => panic!("Response should be residual"),
            PartialResponse::Residual(res) => {
                #[allow(unused_mut)]
                let mut query = translate_response::<Alias>(
                    &res,
                    &get_schema(),
                    InByTable::<Alias, Alias, _>(|_, _| {
                        panic!("There should not be any in's in the residual")
                    }),
                    |_| panic!("There should not be any tables in the residual"),
                )
                .expect("Failed to translate response");
                let query = query
                    .into_select_statement()
                    .column(sea_query::Asterisk)
                    .from(Alias::new("people"))
                    .to_string(SqliteQueryBuilder);
                assert_eq!(
                    query,
                    r#"SELECT * FROM "people" WHERE TRUE AND (TRUE AND 20 <= "age" AND "age" <= 30) AND TRUE"#
                );
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
                let mut query = translate_response(
                    &res,
                    &schema,
                    InByTable::<Alias, Alias, _>(|_, _| {
                        panic!("There should not be any in's in the residual")
                    }),
                    |tp| {
                        (
                            if *tp == *USERS_TYPE {
                                Idens::Users
                            } else if *tp == *PHOTOS_TYPE {
                                Idens::Photos
                            } else {
                                panic!("Unknown type")
                            },
                            "uid".into(),
                        )
                    },
                )
                .expect("Failed to translate response");
                query
                    .query_default_attr("title")
                    .expect("Query should have exactly one unknown");
                let query = query.to_string_sqlite();
                assert_eq!(
                    query,
                    r#"SELECT "resource"."title" FROM "photos" AS "resource" LEFT JOIN "users" AS "temp__0" ON "resource"."user_id" = "temp__0"."uid" WHERE TRUE AND (TRUE AND "temp__0"."name" = 'Alice') AND TRUE"#
                );

                let conn = Connection::open(&*DB_PATH).expect("Connection failed");
                conn.query_row(&query, [], |row| {
                    assert_eq!(
                        row.get::<_, String>(0)
                            .expect("Row should have title column"),
                        "Beach photo"
                    );
                    Ok(())
                })
                .expect("Failed to query");
            }
        }
    }

    #[test]
    fn test_ancestors() {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");

        let ancestors = USERS_TEAMS_MEMBERSHIP_INFO
            .get_ancestors(&conn, &"1".parse().unwrap(), &TEAMS_TYPE)
            .expect("Failed to get ancestors");
        assert!(ancestors.contains(&"Teams::\"0\"".parse().unwrap()));

        assert!(USERS_TEAMS_MEMBERSHIP_INFO
            .is_ancestor(&conn, &"1".parse().unwrap(), &"0".parse().unwrap())
            .expect("Failed to check ancestor"));

        assert!(!USERS_TEAMS_MEMBERSHIP_INFO
            .is_ancestor(&conn, &"0".parse().unwrap(), &"1".parse().unwrap())
            .expect("Failed to check ancestor"));
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
    use std::collections::HashSet;

    use cedar_policy::{
        Authorizer, Decision, EntityAttrAccessError, EntityAttrDatabase, EntityId, EntityTypeName,
        EntityUid, PartialResponse, PartialValue, PolicySet, Request, Response, Schema,
    };

    use rusqlite::Connection;

    use crate::{
        expr_to_query::InByTable,
        idens::Idens,
        query_builder::translate_response,
        sql_common::{AncestorSQLInfo, DatabaseToCedarError, EntitySQLId, EntitySQLInfo},
        sqlite::*,
    };

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "test/docs_example.db";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref DOCS_TYPE: EntityTypeName = "Documents".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<SQLiteSQLInfo> = EntitySQLInfo::simple(Idens::Users, vec!["role"], None::<Idens>);
        static ref DOCS_TABLE_INFO: EntitySQLInfo<SQLiteSQLInfo> = EntitySQLInfo::simple(Idens::Docs, vec!["title", "owner"], None::<Idens>);
        static ref TEAMS_TABLE_INFO: EntitySQLInfo<SQLiteSQLInfo> = EntitySQLInfo::simple(Idens::Teams, vec!["name"], None::<Idens>);

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<SQLiteSQLInfo> = AncestorSQLInfo::new(Idens::UsersInTeams, Idens::UserUid, Idens::TeamUid);
    }

    struct Table {
        conn: Connection,
    }

    impl EntityAttrDatabase for Table {
        type Error = DatabaseToCedarError;

        fn partial_mode(&self) -> cedar_policy::Mode {
            cedar_policy::Mode::Concrete
        }

        fn exists_entity(&self, uid: &EntityUid) -> Result<bool, Self::Error> {
            Ok(get_table_info(uid.type_name())
                .map(|info| info.exists_entity(&self.conn, uid.id()))
                .transpose()?
                .unwrap_or(false))
        }

        fn entity_attr<'e>(
            &'e self,
            uid: &EntityUid,
            attr: &str,
        ) -> Result<PartialValue, EntityAttrAccessError<Self::Error>> {
            let table_info =
                get_table_info(uid.type_name()).ok_or(EntityAttrAccessError::UnknownEntity)?;
            // Unfortunately, we currently do not have schema-based attribute fetching
            // so the Cedar type of the attribute is simply based on the SQL type of the
            // column in the database. This means we have to manually convert the attributes
            // that are not strings but actually `EntityUid`'s
            if uid.type_name() == &*DOCS_TYPE && attr == "owner" {
                Ok(table_info
                    .get_single_attr_as_id(&self.conn, uid.id(), attr, USERS_TYPE.clone())?
                    .into())
            } else {
                Ok(table_info
                    .get_single_attr(&self.conn, uid.id(), attr)?
                    .into())
            }
        }

        fn entity_in(&self, u1: &EntityUid, u2: &EntityUid) -> Result<bool, Self::Error> {
            if u1.type_name() == &*USERS_TYPE && u2.type_name() == &*TEAMS_TYPE {
                USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&self.conn, u1.id(), u2.id())
            } else {
                Ok(false)
            }
        }
    }

    fn get_table_info(tp: &EntityTypeName) -> Option<&EntitySQLInfo<SQLiteSQLInfo>> {
        match tp {
            t if *t == *USERS_TYPE => Some(&USERS_TABLE_INFO),
            t if *t == *DOCS_TYPE => Some(&DOCS_TABLE_INFO),
            t if *t == *TEAMS_TYPE => Some(&TEAMS_TABLE_INFO),
            _ => None,
        }
    }

    fn get_sqlite_table() -> Table {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");

        Table { conn }
    }

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
        "#
        .parse()
        .expect("Document schema should parse correctly")
    }

    fn get_policies_docs_example() -> PolicySet {
        r#"
        // Anyone can see their own documents
        permit(principal, action, resource) when {
            principal == resource.owner
        };

        // Any vp can see any documents made by interns
        permit(principal, action, resource) when {
            principal.role == "vp" && resource.owner.role == "intern"
        };

        // The document with id 'doc4' is shared with everyone in Cedar
        permit(principal in Teams::"cedar", action, resource == Documents::"doc4");
        "#
        .parse()
        .expect("Policies should parse correctly")
    }

    fn can_danielle_view(doc: &str) -> Response {
        let pset = get_policies_docs_example();

        let auth = Authorizer::new();
        let q: Request = Request::builder()
            .principal(Some("Users::\"danielle\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource(Some(EntityUid::from_type_name_and_id(
                DOCS_TYPE.clone(),
                doc.parse().unwrap(),
            )))
            .build();

        auth.is_authorized_full_parsed(&q, &pset, &get_sqlite_table())
    }

    #[test]
    fn test_danielle_views() {
        // Danielle can view doc1 because she is the owner
        assert!(can_danielle_view("doc1").decision() == Decision::Allow);
        // Danielle can view doc2 because she is a vp and doc2 is owned by an intern
        assert!(can_danielle_view("doc2").decision() == Decision::Allow);
        // Danielle cannot view doc3
        assert!(can_danielle_view("doc3").decision() == Decision::Deny);
        // Danielle can view doc4 because it is shared with everyone in Cedar
        assert!(can_danielle_view("doc4").decision() == Decision::Allow);
    }

    #[test]
    fn test_daneille_partial_view() {
        let pset = get_policies_docs_example();
        let auth = Authorizer::new();
        let schema = get_schema();
        let table = get_sqlite_table();

        let q: Request = Request::builder()
            .principal(Some("Users::\"danielle\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource_type("Documents".parse().unwrap())
            .build();

        let result = auth.is_authorized_parsed(&q, &pset, &table);
        match result {
            PartialResponse::Concrete(_) => panic!("Response should be residual"),
            PartialResponse::Residual(resp) => {
                let mut query = translate_response(
                    &resp,
                    &schema,
                    InByTable(|tp1, tp2| {
                        Ok(if tp1 == &*USERS_TYPE && tp2 == &*TEAMS_TYPE {
                            Some((Idens::UsersInTeams, Idens::UserUid, Idens::TeamUid))
                        } else {
                            None
                        })
                    }),
                    |tp| {
                        (
                            get_table_info(tp)
                                .expect("Entity type should be one of known entity types")
                                .table
                                .clone(),
                            "uid".into(),
                        )
                    },
                )
                .expect("Failed to translate response");
                query
                    .query_default()
                    .expect("Query should have exactly one unknown");
                query.query_default_attr("title").unwrap();

                let query_str = query.to_string_sqlite();
                // assert_eq!(query_str, r#"SELECT "resource"."uid", "resource"."title" FROM "docs" AS "resource" LEFT JOIN "users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE ((TRUE AND "resource"."uid" = 'doc4' AND TRUE) OR (TRUE AND 'danielle' = "resource"."owner") OR (TRUE AND (TRUE AND "temp__0"."role" = 'intern'))) AND TRUE"#);

                let mut stmt = table
                    .conn
                    .prepare(&query_str)
                    .expect("Failed to parse query");
                let query_result = stmt
                    .query_map([], |row| {
                        let id: EntitySQLId = row.get(0)?;
                        let title: String = row.get(1)?;
                        Ok((id.id(), title))
                    })
                    .expect("Failed to execute query")
                    .collect::<Result<HashSet<(EntityId, String)>, _>>()
                    .expect("Failed to get columns of row in the requested types");
                assert!(
                    query_result
                        == vec![
                            ("doc1".parse().unwrap(), "Super secret info".into()),
                            ("doc2".parse().unwrap(), "Regular old intern stuff".into()),
                            (
                                "doc4".parse().unwrap(),
                                "Cedar partial evaluation proposal".into()
                            ),
                        ]
                        .into_iter()
                        .collect()
                );
            }
        }
    }
}
