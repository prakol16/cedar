//! This file defines extra functionality that should be added to the sea_query crate.

use sea_query::{ColumnRef, DynIden, IntoIden, IntoTableRef, Query, SimpleExpr, TableRef};

/// Unlike TableRef, this contains only types that can be adjoined to a column to produce a ColumnRef
#[derive(Debug, Clone, PartialEq)]
pub enum StaticTableRef {
    /// A table reference based on an indentifier
    Table(DynIden),
    /// A table reference based on a schema and an identifier
    SchemaTable(DynIden, DynIden),
    // TODO: add database schema table
    // Unfortunately, sea-query does not support DatabaseSchemaTableColumn for ColumnRef
}

impl IntoTableRef for StaticTableRef {
    fn into_table_ref(self) -> sea_query::TableRef {
        match self {
            StaticTableRef::Table(t) => TableRef::Table(t),
            StaticTableRef::SchemaTable(s, t) => TableRef::SchemaTable(s, t),
        }
    }
}

impl<T: IntoIden> From<T> for StaticTableRef {
    fn from(t: T) -> Self {
        StaticTableRef::Table(t.into_iden())
    }
}

impl StaticTableRef {
    /// Append the column to this table reference to create a fully expanded column reference (i.e. with the table)
    pub fn with_column(self, col: impl IntoIden) -> ColumnRef {
        match self {
            StaticTableRef::Table(t) => ColumnRef::TableColumn(t, col.into_iden()),
            StaticTableRef::SchemaTable(s, t) => {
                ColumnRef::SchemaTableColumn(s, t, col.into_iden())
            }
        }
    }

    // pub fn with_asterisk(self) -> ColumnRef {
    //     match self {
    //         StaticTableRef::Table(t) => ColumnRef::TableAsterisk(t),
    //         StaticTableRef::SchemaTable(s, t) => ColumnRef::SchemaTableAsterisk(s, t),
    //     }
    // }
}

/// An optional insert statement is an insert statement
/// which also keeps track of whether it has any values or not
/// This is because an insert statement with no values is a syntax error
#[derive(Debug, Clone, PartialEq, Default)]
pub struct OptionalInsertStatement {
    insert: sea_query::InsertStatement,
    has_values: bool,
}

impl OptionalInsertStatement {
    /// Create a new optional insert statement
    pub fn new() -> Self {
        Self {
            insert: Query::insert(),
            has_values: false,
        }
    }

    /// Convert this optional insert statement into a regular insert statement
    pub fn into_insert_statement(self) -> sea_query::InsertStatement {
        self.insert
    }

    /// Set the table for this insert statement
    pub fn into_table<T: IntoTableRef>(&mut self, tbl_ref: T) {
        self.insert.into_table(tbl_ref);
    }

    /// Set the columns for this insert statement
    pub fn columns<C: IntoIden, I: IntoIterator<Item = C>>(&mut self, cols: I) {
        self.insert.columns(cols);
    }

    /// Add values to this insert statement
    /// Also sets the internal has_values to true
    pub fn values<I: IntoIterator<Item = SimpleExpr>>(
        &mut self,
        vals: I,
    ) -> Result<(), sea_query::error::Error> {
        self.insert.values(vals)?;
        self.has_values = true;
        Ok(())
    }

    /// True if `values` was called on this insert statement and there are a nonzero number of values
    /// being inserted.
    pub fn has_values(&self) -> bool {
        self.has_values
    }
}

#[cfg(test)]
mod test {
    use sea_query::{ArrayType, Expr, PostgresQueryBuilder, Query, SimpleExpr, Value};

    #[test]
    fn test_empty_array() {
        let empty_array: SimpleExpr =
            Value::Array(ArrayType::BigInt, Some(Box::new(vec![]))).into();
        let equality_check = empty_array.clone().eq(empty_array);
        let query = Query::select().expr(Expr::expr(equality_check)).to_owned();
        println!("query: {}", query.to_string(PostgresQueryBuilder));
    }

    // #[test]
    // fn test_build_ambiguous_types() {
    //     let mut conn = Client::connect("host=localhost user=postgres dbname=example_postgres password=postgres", NoTls)
    //         .expect("Should succeed in connecting to postgres db");
    //     let query = Query::select()
    //         .expr(Expr::val(3).eq(3))
    //         .to_owned();
    //     let (query, values) = query.build_postgres(PostgresQueryBuilder);
    //     assert_eq!(query, "SELECT $1 = $2");

    //     let result: bool = conn.query_one("SELECT $1::integer = $2", &values.as_params())
    //         .expect("query with explicit casts should succeed")
    //         .get(0);
    //     assert!(result); // succeeds

    //     let result: bool = conn.query_one(&query, &values.as_params())
    //         .expect("regular query should also succeed")
    //         .get(0); // fails
    //     assert!(result);
    // }

    // #[test]
    // fn test_wrong_type_build() {
    //     let mut conn = Client::connect("host=localhost user=postgres dbname=example_postgres password=postgres", NoTls)
    //         .expect("Should succeed in connecting to postgres db");
    //     let query = Query::select()
    //         .expr(Expr::val("testing text"))
    //         .to_owned();
    //     let query2 = Query::select()
    //         .expr(Expr::val(42))
    //         .to_owned();
    //     let (query, values) = query.build_postgres(PostgresQueryBuilder);
    //     let (query2, values2) = query2.build_postgres(PostgresQueryBuilder);
    //     assert_eq!(query, "SELECT $1");
    //     assert_eq!(query2, "SELECT $1");
    //     let result: String = conn.query_one(&query, &values.as_params())
    //         .expect("regular query should succeed")
    //         .get(0);
    //     assert_eq!(result, "testing text"); // succeeds

    //     let err = conn.query_one(&query, &values2.as_params())
    //         .expect_err("query with wrong type should fail");
    //     println!("error: {:?}", err);
    // }

    #[test]
    fn test_substitute_char() {
        let ch: SimpleExpr = '\u{1a}'.into();
        let query = Query::select().expr(ch).to_owned();
        assert_eq!(query.to_string(PostgresQueryBuilder), r#"SELECT ''"#);
    }
}
