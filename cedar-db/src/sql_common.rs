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

//! This module builds queries for Cedar entities using the sea-query crate
//! It also contains utilities for converting between Cedar data and database data
use std::{
    collections::{HashMap, HashSet},
    marker::PhantomData,
};

use cedar_policy::{EntityId, EntityTypeName, EntityUid, Value};
use cedar_policy_core::{
    ast::{Literal, NotValue},
    entities::{JSONValue, JsonDeserializationError},
    evaluator::RestrictedEvaluator,
    extensions::Extensions,
};
use ref_cast::RefCast;
use sea_query::{
    Alias, ArrayType, ColumnRef, Expr, IntoColumnRef, IntoTableRef, Nullable, Query,
    SelectStatement, TableRef,
};
use smol_str::SmolStr;
use thiserror::Error;

use crate::query_expr::{QueryPrimitiveType, QueryType};

/// An SQLValue is a wrapper around a Cedar value that implements FromSql
/// Note: None corresponds to NULL in the database
#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
pub struct SQLValue(pub(crate) Option<Value>);

impl From<QueryPrimitiveType> for ArrayType {
    fn from(value: QueryPrimitiveType) -> Self {
        match value {
            QueryPrimitiveType::Bool => ArrayType::Bool,
            QueryPrimitiveType::Long => ArrayType::BigInt,
            QueryPrimitiveType::StringOrEntity => ArrayType::String,
            QueryPrimitiveType::Record => ArrayType::Json,
        }
    }
}

/// Given a type, return the null value of that type
pub fn null_value_of_type(ty: QueryType) -> sea_query::Value {
    match ty {
        QueryType::Primitive(QueryPrimitiveType::Bool) => bool::null(),
        QueryType::Primitive(QueryPrimitiveType::Long) => i64::null(),
        QueryType::Primitive(QueryPrimitiveType::StringOrEntity) => String::null(),
        QueryType::Primitive(QueryPrimitiveType::Record) => serde_json::Value::null(),
        QueryType::Array(p) => sea_query::Value::Array(p.into(), None),
    }
}

/// Given a value, convert it to a JSON value
/// The difference between this and `JSONValue::from_expr` is that the latter
/// uses escapes to encode entity uids and extension functions. This, however,
/// simply encodes entity uids as strings (keeping only the ids), and extensions as null
/// In particular, note that this transformation is not reversible
pub fn value_to_json_value(v: &Value) -> serde_json::Value {
    match v {
        Value::Lit(Literal::Bool(b)) => (*b).into(),
        Value::Lit(Literal::Long(i)) => (*i).into(),
        Value::Lit(Literal::String(s)) => s.as_str().into(),
        Value::Lit(Literal::EntityUID(uid)) => {
            let uid_str: &str = uid.eid().as_ref();
            uid_str.into()
        }
        Value::Set(s) => s.iter().map(value_to_json_value).collect(),
        Value::Record(r) => r
            .iter()
            .map(|(k, v)| (k.to_string(), value_to_json_value(v)))
            .collect(),
        Value::ExtensionValue(_) => serde_json::Value::Null,
    }
}

/// Given a Cedar value and its type as a QueryType, convert it to a sea_query value
pub fn value_to_sea_query_value(v: &Value, ty: QueryType) -> sea_query::Value {
    match v {
        Value::Lit(Literal::Bool(b)) => (*b).into(),
        Value::Lit(Literal::Long(i)) => (*i).into(),
        Value::Lit(Literal::String(s)) => s.as_str().into(),
        Value::Lit(Literal::EntityUID(uid)) => {
            let uid_str: &str = uid.eid().as_ref();
            uid_str.into()
        }
        Value::Set(s) => {
            let prim = ty.get_type(); // get the primitive type of the set
            sea_query::Value::Array(
                prim.into(),
                Some(Box::new(
                    s.iter()
                        .map(|v| value_to_sea_query_value(v, prim.into()))
                        .collect(),
                )),
            )
        }
        Value::Record(_) => value_to_json_value(v).into(),
        // TODO: we can convert certain extension functions to values
        // e.g. ip can be converted to native ip types, similarly with datetime, decimal -> int/bigdecimal, etc.
        Value::ExtensionValue(_) => sea_query::Value::String(None),
    }
}

/// An EntitySQLId is a wrapper around an EntityId that implements FromSql
#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
pub struct EntitySQLId(pub(crate) EntityId);

impl EntitySQLId {
    /// Get the underlying EntityId of the EntitySQLId
    pub fn id(self) -> EntityId {
        self.0
    }

    /// Convenience method to convert a uid into an EntityUid given a type name
    pub fn into_uid(self, tp: EntityTypeName) -> EntityUid {
        EntityUid::from_type_name_and_id(tp, self.id())
    }
}

/// An error occurs while trying to convert database data to Cedar data
#[derive(Debug, Error)]
pub enum DatabaseToCedarError {
    /// Occurs when database returns an ancestor field that is not a json array
    #[error("Ancestor field is not a json array")]
    AncestorNotJsonArray,

    /// Miscellaneous database error (e.g. connection error)
    #[cfg(feature = "postgres")]
    #[error("Database had error: {0}")]
    PostgresError(#[from] postgres::Error),

    /// Miscellaneous database error (e.g. connection error)
    #[cfg(feature = "rusqlite")]
    #[error("Database had error: {0}")]
    SqliteError(#[from] rusqlite::Error),

    /// Error when deserializing JSON to entity attribute data
    #[error("Json deserialization error: {0}")]
    JsonDeserializationError(#[from] JsonDeserializationError),

    /// Error when evaluating the restricted expression for entity attribute data fails
    #[error("Error when evaluating expression attributes in JSON: {0}")]
    ExpressionEvaluationError(#[from] cedar_policy_core::evaluator::EvaluationError),

    /// Error when evaluating the restricted expression for entity attribute data results in partial value
    #[error("Attribute evaluation resulted in residual")]
    NotValue(#[from] NotValue),
}

type Result<T> = std::result::Result<T, DatabaseToCedarError>;

impl From<serde_json::Error> for DatabaseToCedarError {
    /// Convert a serde_json::Error to a DatabaseToCedarError
    fn from(value: serde_json::Error) -> Self {
        Self::JsonDeserializationError(value.into())
    }
}

impl<T: Into<Value>> From<T> for SQLValue {
    /// Convert anything that can be converted to a value to an `SQLValue`
    fn from(v: T) -> Self {
        SQLValue(Some(v.into()))
    }
}

impl SQLValue {
    /// Attempt to convert JSON into an SQLValue
    /// Note: This does parses entity escapes and handles them as a special case
    /// Moreover, it also evaluations extension functions in expression attributes
    pub fn from_json(v: serde_json::Value) -> Result<Self> {
        if v.is_null() {
            Ok(SQLValue(None))
        } else {
            let jvalue: JSONValue = serde_json::from_value(v)?;
            let rexpr = jvalue.into_expr()?;
            let all_exts = Extensions::all_available();
            let reval = RestrictedEvaluator::new(&all_exts);
            let val = reval.partial_interpret(rexpr.as_borrowed())?;
            Ok(SQLValue(Some(val.try_into()?)))
        }
    }
}

/// This structure stores information about a particular entity type stored in some table in the database
/// We assume that the table has a column corresponding to the id of the entity
/// and that the table has columns corresponding to the attributes of the entity
#[derive(Debug, Clone)]
pub struct EntitySQLInfo<U: IsSQLDatabase> {
    /// The table that the entities are stored in
    pub table: TableRef,

    /// The column that the id of the entity is stored in
    pub id_attr: ColumnRef,

    /// The columns that the attributes of the entity are stored in
    pub sql_attr_names: Vec<ColumnRef>,

    /// The attributes of the entity; each (index, name) pair indicates
    /// that the attribute with name `name` is the `index`th attribute of the query result
    /// (i.e. the `index`th attribute of `sql_attr_names`)
    ///
    /// A good default behavior of associating `attr_names` with `sql_attr_names` is provided by the
    /// `EntitySQLInfo::simple` method.
    /// However, you can add additional attributes to your entity using the `make_entity_extra_attrs`
    /// method which will be provided the entire query row result. This is useful if your entity has
    /// attributes that are non-trivial functions of the data in the database.
    pub attr_names_map: HashMap<SmolStr, usize>,

    /// The index (in `sql_attr_names`) of the column that stores the ancestors of the entity
    /// If this is not how ancestry information is stored, leave this as `None`
    pub ancestor_attr_ind: Option<usize>,

    phantom: PhantomData<U>,
}

/// This trait is used to indicate that a type is used for SQL database information
/// It helps keep track of which information is relevant to which kind of database
pub trait IsSQLDatabase {}

impl<U: IsSQLDatabase> EntitySQLInfo<U> {
    /// Construct a new EntitySQLInfo from the given information
    pub fn new(
        table: TableRef,
        id_attr: ColumnRef,
        sql_attr_names: Vec<ColumnRef>,
        attr_names_map: HashMap<SmolStr, usize>,
        ancestor_attr_ind: Option<usize>,
    ) -> Self {
        Self {
            table,
            id_attr,
            sql_attr_names,
            attr_names_map,
            ancestor_attr_ind,
            phantom: PhantomData,
        }
    }

    /// Construct a new EntitySQLInfo from the given information
    /// This is a convenience method for when the attribute names are the same as the column names
    /// and the id column is "uid"
    pub fn simple(
        table: impl IntoTableRef,
        attr_names: Vec<&str>,
        ancestor_attr: Option<impl IntoColumnRef>,
    ) -> Self {
        let table = table.into_table_ref();
        let ancestor_attr = ancestor_attr.map(|x| x.into_column_ref());

        let mut sql_attr_names = attr_names
            .iter()
            .map(|s| Alias::new(*s).into_column_ref())
            .collect::<Vec<_>>();
        if let Some(ancestor_attr_val) = ancestor_attr.clone() {
            sql_attr_names.push(ancestor_attr_val);
        }

        let len = attr_names.len();
        let attr_names = attr_names
            .into_iter()
            .enumerate()
            .map(|(k, v)| (SmolStr::from(v), k))
            .collect::<HashMap<SmolStr, usize>>();

        Self::new(
            table,
            Alias::new("uid").into_column_ref(),
            sql_attr_names,
            attr_names,
            ancestor_attr.map(|_| len),
        )
    }

    fn select_all_cols(&self, select: &mut SelectStatement) {
        // If there are no columns, we add a dummy column
        // to the select statement to prevent a syntax error
        if self.sql_attr_names.is_empty() {
            select.expr(1);
        } else {
            select.columns(self.sql_attr_names.clone());
        }
    }

    fn from_where(&self, select: &mut SelectStatement, id: &str) {
        select.from(self.table.clone());
        select.and_where(Expr::col(self.id_attr.clone()).eq(id));
    }

    /// Get the select statement which returns the single attribute `attr`
    /// Returns None if `attr` was not found
    pub fn get_single_attr_select(&self, id: &EntityId, attr: &str) -> Option<SelectStatement> {
        let mut select = Query::select();
        let ind = *self.attr_names_map.get(attr)?;
        select.column(self.sql_attr_names.get(ind)?.clone());
        self.from_where(&mut select, id.as_ref());
        Some(select)
    }

    /// Get the select statement which returns a single row with no data iff the entity exists
    pub fn get_exists_select(&self, id: &EntityId) -> SelectStatement {
        let mut select = Query::select();
        select.expr(Expr::value(1));
        self.from_where(&mut select, id.as_ref());
        select
    }

    /// Get the select statement which returns the row and all of the attributes
    pub fn get_select(&self, id: &EntityId) -> SelectStatement {
        let mut select = Query::select();
        self.select_all_cols(&mut select);
        self.from_where(&mut select, id.as_ref());
        select
    }
}

// Make the ancestor set given the JSON representing the ancestors
pub(crate) fn make_ancestors(ancestors: serde_json::Value) -> Result<HashSet<EntityUid>> {
    ancestors
        .as_array()
        .ok_or(DatabaseToCedarError::AncestorNotJsonArray)?
        .iter()
        .map(|x| Ok(EntityUid::from_json(x.clone())?))
        .collect()
}

/// This structure stores information about how ancestor information is stored in a database
/// Specifically, it assumes that there is a table with two columns such that each row is an edge
/// in the ancestor graph (i.e. each row is of the form (a, b) where a is a descendant of b)
#[derive(Debug, Clone)]
pub struct AncestorSQLInfo<U: IsSQLDatabase> {
    /// The table containing the ancestry information
    pub table: TableRef,
    /// The column containing the child id
    pub child_id: ColumnRef,
    /// The column containing the parent id
    pub parent_id: ColumnRef,
    phantom: PhantomData<U>,
}

impl<U: IsSQLDatabase> AncestorSQLInfo<U> {
    /// Construct a new AncestorSQLInfo from the given information
    pub fn new(
        table: impl IntoTableRef,
        child_id: impl IntoColumnRef,
        parent_id: impl IntoColumnRef,
    ) -> Self {
        Self {
            table: table.into_table_ref(),
            child_id: child_id.into_column_ref(),
            parent_id: parent_id.into_column_ref(),
            phantom: PhantomData,
        }
    }

    /// Get the select statement which returns all of the parents of the given child
    pub fn query_all_parents(&self, child_id: &EntityId) -> SelectStatement {
        let mut select = Query::select();
        select.column(self.parent_id.clone());
        select.from(self.table.clone());
        select.and_where(Expr::col(self.child_id.clone()).eq(child_id.as_ref()));
        select
    }

    /// Get the select statement which returns a single row with no data iff the child is a descendant of the parent
    pub fn query_is_parent(&self, child_id: &EntityId, parent_id: &EntityId) -> SelectStatement {
        let mut select = Query::select();
        select.expr(Expr::value(1));
        select.from(self.table.clone());
        select.and_where(Expr::col(self.child_id.clone()).eq(child_id.as_ref()));
        select.and_where(Expr::col(self.parent_id.clone()).eq(parent_id.as_ref()));
        select
    }
}
