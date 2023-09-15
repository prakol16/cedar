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

pub mod sql_common;

#[cfg(feature = "rusqlite")]
pub mod sqlite;

#[cfg(feature = "postgres")]
pub mod postgres;

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
    }
}

#[cfg(feature = "postgres")]
#[cfg(test)]
mod test_postgres {
    use std::borrow::Cow;

    use cedar_policy::{
        Authorizer, CachedEntities, Context, Decision, EntityAttrAccessError, EntityDataSource,
        WholeEntityDataSource, EntityTypeName, EntityUid, PartialValue, Request,
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

    fn make_entity_attr_database() -> impl EntityDataSource {
        struct Table;

        impl EntityDataSource for Table {
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

        impl WholeEntityDataSource for Table {
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
        Authorizer, Context, Decision, WholeEntityDataSource, EntityTypeName, EntityUid, Request,
    };

    use rusqlite::Connection;

    use crate::{
        idens::Idens,
        sql_common::{AncestorSQLInfo, DatabaseToCedarError, EntitySQLInfo},
        sqlite::*,
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

    fn get_sqlite_table() -> impl WholeEntityDataSource {
        let conn = get_conn();
        struct Table {
            conn: Connection,
        }

        impl WholeEntityDataSource for Table {
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
