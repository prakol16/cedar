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

    use cedar_policy::{EntityUid, EntityTypeName, Authorizer, Request, Context, EntityDatabase, EvaluationError, EntityAttrDatabase, PartialValue, EntityAttrAccessError, CachedEntities};
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

        fn get_entity_attrs(uid: &EntityUid) -> Result<Option<HashMap<String, PartialValue>>, EvaluationError> {
            let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
            match uid.type_name() {
                t if *t == *USERS_TYPE =>
                    conn.query_opt(USERS_TABLE_INFO.get_query_string(), &[&uid.id().as_ref()])
                    .map_err(EvaluationError::mk_err)?
                    .map(|row| convert_attr_names(&row, &USERS_TABLE_INFO.attr_names).map_err(EvaluationError::StringMessage))
                    .transpose(),
                t if *t == *PHOTOS_TYPE =>
                    conn.query_opt(PHOTOS_TABLE_INFO.get_query_string(), &[&uid.id().as_ref()])
                    .map_err(EvaluationError::mk_err)?
                    .map(|row| convert_attr_names(&row, &PHOTOS_TABLE_INFO.attr_names).map_err(EvaluationError::StringMessage))
                    .transpose(),
                _ => Ok(None)
            }
        }

        impl EntityAttrDatabase for Table {
            fn exists_entity(&self, uid: &EntityUid) -> Result<bool, EvaluationError> {
                Ok(get_entity_attrs(uid)?.is_some())
            }

            fn entity_attr<'e>(&'e self, uid: &EntityUid, attr: &str) -> Result<PartialValue, EntityAttrAccessError<EvaluationError>> {
                get_entity_attrs(uid)?
                .ok_or(EntityAttrAccessError::UnknownEntity)
                .and_then(|attrs| attrs.get(attr).cloned().ok_or(EntityAttrAccessError::UnknownAttr))
            }

            fn entity_in(&self, u1: &EntityUid, u2: &EntityUid) -> Result<bool, EvaluationError> {
                match (u1.type_name(), u2.type_name()) {
                    (t1, t2) if *t1 == *USERS_TYPE && *t2 == *TEAMS_TYPE => {
                        let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                        USERS_TEAMS_MEMBERSHIP_INFO.is_ancestor(&mut conn, u1.id(), u2.id())
                        .map_err(EvaluationError::StringMessage)
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
            fn get<'e>(&'e self, uid: &EntityUid) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, EvaluationError> {
                let mut conn = Client::connect(&*DB_PATH, NoTls).expect("Connection failed");
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO.make_entity_ancestors(&mut conn, uid).map_err(EvaluationError::StringMessage)?.map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO.make_entity_ancestors(&mut conn, uid).map_err(EvaluationError::StringMessage)?.map(Cow::Owned)),
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

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName, EvaluationError};

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

    fn get_sqlite_table() -> impl EntityDatabase {
        let conn = Connection::open(&*DB_PATH).expect("Connection failed");
        struct Table { conn: Connection }

        impl EntityDatabase for Table {
            fn get<'e>(&'e self, uid: &EntityUid) -> Result<Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>>, EvaluationError> {
                match uid.type_name() {
                    t if *t == *USERS_TYPE => Ok(USERS_TABLE_INFO.make_entity_ancestors(&self.conn, uid).map_err(EvaluationError::mk_err)?.map(Cow::Owned)),
                    t if *t == *PHOTOS_TYPE => Ok(PHOTOS_TABLE_INFO.make_entity_ancestors(&self.conn, uid).map_err(EvaluationError::mk_err)?.map(Cow::Owned)),
                    _ => Ok(None)
                }
            }

            fn partial_mode(&self) -> cedar_policy::Mode {
                cedar_policy::Mode::Concrete
            }
        }

        Table { conn }
    }

    /*
    #[test]
    fn test_partial_eval_policies() {
        let auth = Authorizer::new();
        let req: Request = Request::builder()
            .principal(Some("Users::\"0\"".parse().unwrap()))
            .action(Some("Actions::\"view\"".parse().unwrap()))
            .resource_type("Photos".parse().unwrap())
            .build();
        println!("Request: {:?}", req);
        let result = auth.is_authorized_parsed(&req,
            &r#"permit(principal, action, resource) when { principal == resource.user_id && principal.name == "Alice" };"#.parse().unwrap(),
            &get_sqlite_table());
        println!("\n\n\nResult of authorization: {:?}", result);
        println!("\n\n");
        match result {
            PartialResponse::Concrete(dec) => println!("Got response {dec:?}"),
            PartialResponse::Residual(resp) => {
                println!("Translating residual response into query: {}",
                    translate_residual_policies(resp, &Schema(get_schema()),
                    &|_, _| Ok((Alias::new("team_memberships"), Alias::new("user_uid"), Alias::new("team_uid"))))
                    .into_values()
                    .map(|q| Query::select()
                        .column(Asterisk)
                        .from_as(Alias::new("photos"), Alias::new("resource"))
                        .and_where(q)
                        .to_string(SqliteQueryBuilder))
                    .collect::<Vec<_>>()
                    .join("\n"));
            }
        };
    }
    */

    /*
    #[test]
    fn test_partial_eval_expr() {
        // let photos_type: Type = Type::Entity { ty: EntityType::Concrete("Photos".parse().unwrap()) };
        let extensions = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&extensions);
        let test_expr: Expr =
            eval.partial_interpret_unrestricted(
                &r#"unknown("photos: Photos").owner == Users::"0""#.parse().expect("Failed to parse expression"),
                &["unknown".parse().unwrap()].into(),
            ).unwrap();
        let schema = get_schema();
        let req_env = RequestEnv {
            principal: &EntityType::Concrete("Users".parse().unwrap()),
            action: &r#"Action::"view""#.parse().unwrap(),
            resource: &EntityType::Concrete("Photos".parse().unwrap()),
            context: &Attributes::default()
        };
        let typechecker = Typechecker::new(&schema, ValidationMode::Strict);
        let typed_test_expr = typechecker.typecheck_expr_strict(
            &req_env, &test_expr, cedar_policy_validator::types::Type::primitive_boolean(), &mut Vec::new())
            .expect("Type checking should succeed");
        println!("{typed_test_expr:?}");

        let translated = expr_to_sql_query_entity_in_table::<Alias, Alias, Alias>(&typed_test_expr, &|_t1, _t2| todo!())
            .expect("Failed to translate expression");
        println!("{}", Query::select()
                        .column(Asterisk)
                        .from(Alias::new("photos"))
                        .and_where(translated)
                        .to_string(SqliteQueryBuilder));

    }
    */

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
        let result = auth.is_authorized_parsed(
            &Request::new(Some(euid.clone()),
                Some("Actions::\"view\"".parse().unwrap()),
                Some("Photos::\"2\"".parse().unwrap()), Context::empty())
            , &"permit(principal, action, resource) when { principal.name == \"Alice\" && resource.title == \"Beach photo\" };".parse().unwrap(),
            &get_sqlite_table());

        println!("Result {:?}", result);
        // TODO: assert(result.decision == Allow)
    }

}