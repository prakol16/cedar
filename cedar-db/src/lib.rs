pub use crate::entity_sql_fetcher::*;

mod entity_sql_fetcher;

#[cfg(test)]
mod test {
    use std::borrow::Cow;

    use cedar_policy::{Authorizer, EntityUid, Request, Context, EntityDatabase, EntityTypeName};

    use rusqlite::Connection;

    use crate::entity_sql_fetcher::*;

    #[cfg(test)]
    lazy_static::lazy_static! {
        static ref USERS_TYPE: EntityTypeName = "Users".parse().unwrap();
        static ref PHOTOS_TYPE: EntityTypeName = "Photos".parse().unwrap();
        static ref TEAMS_TYPE: EntityTypeName = "Teams".parse().unwrap();

        static ref USERS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("users", vec!["name", "age"], Some("ancestors"));
        static ref PHOTOS_TABLE_INFO: EntitySQLInfo<'static> = EntitySQLInfo::simple("photos", vec!["title", "location"], Some("ancestors"));

        static ref USERS_TEAMS_MEMBERSHIP_INFO: AncestorSQLInfo<'static> = AncestorSQLInfo::new("team_memberships", "user", "team");
    }

    #[test]
    fn test_ancestors() {
        let conn = Connection::open("example.db").expect("Connection failed");

        println!("Ancestors: {:?}", USERS_TEAMS_MEMBERSHIP_INFO.get_ancestors(&conn, &"1".parse().unwrap(), &TEAMS_TYPE));
    }

    #[test]
    fn test_basic() {
        let conn = Connection::open("example.db").expect("Connection failed");
        struct Table { conn: Connection }

        impl EntityDatabase for Table {
            fn get<'e>(&'e self, uid: &EntityUid) -> Option<std::borrow::Cow<'e, cedar_policy::ParsedEntity>> {
                match uid.type_name() {
                    t if *t == *USERS_TYPE => USERS_TABLE_INFO.make_entity_ancestors(&self.conn, uid).map(Cow::Owned),
                    t if *t == *PHOTOS_TYPE => PHOTOS_TABLE_INFO.make_entity_ancestors(&self.conn, uid).map(Cow::Owned),
                    t => panic!("Unknown type: {:?}", t)
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