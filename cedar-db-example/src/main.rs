use cedar_policy::{EntityDatabase, EntityId, EntityTypeName, EntityUid, Entity};
use rusqlite::{Connection, Result};


struct SQLiteDB {
    conn: Connection,
}

impl EntityDatabase for SQLiteDB {
    fn get_entity_of_uid(&self, uid: &EntityUid) -> Option<Entity> {
        todo!()
    }

    fn is_partial(&self) -> bool {
        todo!()
    }
}

fn main() {
    println!("Hello, world!");
    create_example_database().unwrap();
}

fn create_example_database() -> Result<()> {
    let conn = Connection::open("cedar-db-example/example.db")?;
    conn.query_row("SELECT name, age FROM users", [], |row| {
        let name: String = row.get(0)?;
        let age: i32 = row.get(1)?;
        println!("found person: {} {}", name, age);
        Ok(())
    })?;
    Ok(())
}
