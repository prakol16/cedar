//! This file defines extra functionality that should be added to the sea_query crate.

use sea_query::{DynIden, IntoTableRef, TableRef, IntoIden, ColumnRef, Query, SimpleExpr};


#[derive(Debug, Clone, PartialEq)]
pub enum StaticTableRef {
    Table(DynIden),
    SchemaTable(DynIden, DynIden),
    // TODO: add database schema table
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
            StaticTableRef::SchemaTable(s, t) => ColumnRef::SchemaTableColumn(s, t, col.into_iden())
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
#[derive(Debug, Clone, PartialEq)]
pub struct OptionalInsertStatement {
    insert: sea_query::InsertStatement,
    has_values: bool,
}

impl OptionalInsertStatement {
    pub fn new() -> Self {
        Self {
            insert: Query::insert(),
            has_values: false,
        }
    }

    pub fn into_insert_statement(self) -> sea_query::InsertStatement {
        self.insert
    }

    pub fn into_table<T: IntoTableRef>(&mut self, tbl_ref: T) {
        self.insert.into_table(tbl_ref);
    }

    pub fn columns<C: IntoIden, I: IntoIterator<Item = C>>(&mut self, cols: I) {
        self.insert.columns(cols);
    }

    pub fn values<I: IntoIterator<Item = SimpleExpr>>(&mut self, vals: I) -> Result<(), sea_query::error::Error> {
        self.insert.values(vals)?;
        self.has_values = true;
        Ok(())
    }

    pub fn has_values(&self) -> bool {
        self.has_values
    }
}