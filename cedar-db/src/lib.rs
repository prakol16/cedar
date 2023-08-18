#[cfg(feature = "rusqlite")]
pub mod sqlite;

#[cfg(feature = "postgres")]
pub mod postgres;

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

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName};

    use rusqlite::Connection;

    use crate::sqlite::*;

    lazy_static::lazy_static! {
        static ref DB_PATH: &'static str = "test/example_sqlite.db";

        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<'static> = AncestorSQLInfo::new("team_memberships", "user", "team");
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

        let auth = Authorizer::new();
        let euid: EntityUid = "Users::\"0\"".parse().unwrap();
        let result = auth.is_authorized_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Photos::\"2\"".parse().unwrap()), Context::empty())
            , &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
            &Table { conn });

        println!("Result {:?}", result);
        // TODO: assert(result.decision == Allow)
    }

}