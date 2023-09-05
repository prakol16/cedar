//! This file defines extra functionality that should be added to the sea_query crate.

use sea_query::{DynIden, IntoTableRef, TableRef, IntoIden, ColumnRef};


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

