use std::collections::{HashMap, HashSet};

use cedar_policy::{Value, ParsedEntity, EntityUid, PartialValue, EntityId, EntityTypeName};
use cedar_policy_core::{entities::{JsonDeserializationError, JSONValue}, evaluator::RestrictedEvaluator, extensions::Extensions, ast::NotValue};
use postgres::{Client, types::{FromSql, Type, Kind}, Row};
use ref_cast::RefCast;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, RefCast)]
#[repr(transparent)]
struct SQLValue(Option<Value>);

#[derive(Debug, Error)]
pub enum PostgresToCedarError {
    #[error("Ancestor field of {0} is not a json array")]
    AncestorNotJsonArray(EntityUid),
    #[error("Database had error: {0}")]
    PostgresError(#[from] postgres::Error),
    #[error("Json deserialization error: {0}")]
    JsonDeserializationError(#[from] JsonDeserializationError),
    #[error("Error when evaluating expression attributes in JSON: {0}")]
    ExpressionEvaluationError(#[from] cedar_policy_core::evaluator::EvaluationError),
    #[error("Attribute evaluation resulted in residual")]
    NotValue(#[from] NotValue)
}

impl From<serde_json::Error> for PostgresToCedarError {
    fn from(value: serde_json::Error) -> Self {
        Self::JsonDeserializationError(value.into())
    }
}

impl<T: Into<Value>> From<T> for SQLValue {
    fn from(v: T) -> Self {
        SQLValue(Some(v.into()))
    }
}

impl SQLValue {
    fn from_json(v: serde_json::Value) -> Result<Self, PostgresToCedarError> {
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

impl<'a> FromSql<'a> for SQLValue {
    fn from_sql(ty: &Type, raw: &'a [u8]) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        if bool::accepts(ty) {
            Ok(bool::from_sql(ty, raw)?.into())
        } else if i32::accepts(ty) {
            Ok((i32::from_sql(ty, raw)? as i64).into())
        } else if i64::accepts(ty) {
            Ok(i64::from_sql(ty, raw)?.into())
        } else if u32::accepts(ty) {
            Ok((u32::from_sql(ty, raw)? as i64).into())
        } else if String::accepts(ty) {
            Ok(String::from_sql(ty, raw)?.into())
        } else if <HashMap<String, Option<String>> as FromSql>::accepts(ty) {
            Ok(<HashMap<String, Option<String>> as FromSql>::from_sql(ty, raw)?
            .into_iter()
            .filter_map(|(k, v)| Some((k, v?.into())))
            .collect::<Vec<(String, Value)>>()
            .into())
        } else if let Kind::Array(inner) = ty.kind() {
            Ok(<Vec<SQLValue> as FromSql>::from_sql(inner, raw)?
                .into_iter()
                .filter_map(|v| v.0)
                .collect::<Vec<Value>>()
                .into())
        } else if <serde_json::Value as FromSql>::accepts(ty) {
            let json = <serde_json::Value as FromSql>::from_sql(ty, raw)?;
            Ok(SQLValue::from_json(json)?)
        } else {
            Err(format!("unsupported type: {:?}", ty).into())
        }
    }

    fn from_sql_null(_ : &Type) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        Ok(SQLValue(None))
    }

    fn accepts(ty: &postgres::types::Type) -> bool {
        bool::accepts(ty) ||
        i32::accepts(ty) ||
        i64::accepts(ty) ||
        u32::accepts(ty) ||
        String::accepts(ty) ||
        <HashMap<String, Option<String>> as FromSql>::accepts(ty) ||
        (match ty.kind() {
            Kind::Array(inner) => <SQLValue as FromSql>::accepts(inner),
            _ => false
        }) ||
        <serde_json::Value as FromSql>::accepts(ty)
    }
}

pub struct EntitySQLId(EntityId);

impl<'a> FromSql<'a> for EntitySQLId {
    fn from_sql(ty: &Type, raw: &'a [u8]) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        if String::accepts(ty) {
            Ok(EntitySQLId((String::from_sql(ty, raw)?).parse().unwrap()))
        } else {
            Err(format!("unsupported type: {:?}", ty).into())
        }
    }

    fn accepts(ty: &Type) -> bool {
        String::accepts(ty)
    }
}

pub struct EntitySQLInfo<'e> {
    pub table: &'e str,
    pub id_attr: &'e str,
    pub sql_attr_names: Vec<&'e str>,
    pub attr_names: Vec<(usize, &'e str)>,
    pub ancestor_attr_ind: Option<usize>,
    query_string: String
}

impl<'e> EntitySQLInfo<'e> {
    pub fn new(table: &'e str, id_attr: &'e str, sql_attr_names: Vec<&'e str>, attr_names: Vec<(usize, &'e str)>, ancestor_attr_ind: Option<usize>) -> Self {
        let attr_names_string: String =
            if sql_attr_names.is_empty() { "*".into() }
            else { sql_attr_names.iter().map(|x| format!("\"{}\"", x)).collect::<Vec<String>>().join(", ") };
        Self {
            table,
            id_attr,
            sql_attr_names,
            attr_names,
            ancestor_attr_ind,
            query_string: format!("SELECT {} FROM \"{}\" WHERE \"{}\" = $1", attr_names_string, table, id_attr)
        }
    }

    pub fn simple(table: &'e str, attr_names: Vec<&'e str>, ancestor_attr: Option<&'e str>) -> Self {
        let mut sql_attr_names: Vec<&'e str> = attr_names.clone();
        if let Some(ancestor_attr) = ancestor_attr {
            sql_attr_names.push(ancestor_attr);
        }

        let len = attr_names.len();
        let attr_names: Vec<(usize, &'e str)> = attr_names.into_iter().enumerate().collect();

        Self::new(table, "uid", sql_attr_names, attr_names, ancestor_attr.map(|_| len))
    }

    pub fn make_entity_ancestors(&self, conn: &mut Client, uid: &EntityUid) -> Result<Option<ParsedEntity>, PostgresToCedarError> {
        self.make_entity(conn, uid, |row| {
            match self.ancestor_attr_ind {
                Some(ancestors_attr_ind) => {
                    row.get::<_, serde_json::Value>(ancestors_attr_ind)
                    .as_array().ok_or_else(|| PostgresToCedarError::AncestorNotJsonArray(uid.clone()))? // TODO: make an error type
                    .iter()
                    .map(|x| {
                        Ok(EntityUid::from_json(x.clone())?)
                    })
                    .collect()
                },
                None => panic!("make_entity_ancestors should only be called when `ancestors_attr_ind` is filled"),
            }
        })
    }

    pub fn get_query_string(&self) -> &str {
        return &self.query_string;
    }

    pub fn make_entity(&self, conn: &mut Client, uid: &EntityUid, ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, PostgresToCedarError>)
        -> Result<Option<ParsedEntity>, PostgresToCedarError> {
        make_entity_from_table(conn, uid, &self.query_string,
            |row| convert_attr_names(&row, &self.attr_names),
            ancestors)
    }

    pub fn make_entity_extra_attrs(&self, conn: &mut Client, uid: &EntityUid, ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, PostgresToCedarError>,
        extra_attrs: impl FnOnce(&Row) -> Result<HashMap<String, PartialValue>, PostgresToCedarError>)
        -> Result<Option<ParsedEntity>, PostgresToCedarError> {
        make_entity_from_table(conn, uid, &self.query_string,
            |row| {
                let mut attrs = convert_attr_names(&row, &self.attr_names)?;
                attrs.extend(extra_attrs(row)?);
                Ok(attrs)
            }, ancestors)
    }
}

pub struct AncestorSQLInfo<'e> {
    pub table: &'e str,
    pub child_id: &'e str,
    pub parent_id: &'e str,
    query_all_string: String,
    query_one_string: String,
}

impl<'e> AncestorSQLInfo<'e> {
    pub fn new(table: &'e str, child_id: &'e str, parent_id: &'e str) -> Self {
        Self {
            table,
            child_id,
            parent_id,
            query_all_string: format!("SELECT \"{}\" FROM \"{}\" WHERE \"{}\" = $1", parent_id, table, child_id),
            query_one_string: format!("SELECT 1 FROM \"{}\" WHERE \"{}\" = $1 AND \"{}\" = $2", table, child_id, parent_id),
        }
    }

    pub fn get_ancestors(&self, conn: &mut Client, id: &EntityId, tp: &EntityTypeName) -> Result<HashSet<EntityUid>, PostgresToCedarError> {
        // TODO: prepare query_string for better performance
        Ok(conn.query(&self.query_all_string, &[&id.as_ref()])?
            .into_iter()
            .map(|row| {
                let parent_id: EntitySQLId = row.get(0);
                EntityUid::from_type_name_and_id(tp.clone(), parent_id.0)
            })
            .collect())
    }

    pub fn is_ancestor(&self, conn: &mut Client, child_id: &EntityId, parent_id: &EntityId) -> Result<bool, PostgresToCedarError> {
        Ok(conn.query_opt(&self.query_one_string, &[&child_id.as_ref(), &parent_id.as_ref()])?.is_some())
    }
}

pub fn convert_attr_names(query_result: &Row, attr_names: &[(usize, &str)]) -> Result<HashMap<String, PartialValue>, PostgresToCedarError> {
    attr_names.iter()
        .filter_map(|(ind, nm)| {
            match query_result.get::<_, SQLValue>(*ind) {
                SQLValue(Some(v)) => Some(Ok((nm.to_string(), v.into()))),
                SQLValue(None) => None
            }
        })
        .collect()
}

pub fn make_entity_from_table(conn: &mut Client, uid: &EntityUid,
    query_string: &str,
    attrs: impl FnOnce(&Row) -> Result<HashMap<String, PartialValue>, PostgresToCedarError>,
    ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, PostgresToCedarError>) -> Result<Option<ParsedEntity>, PostgresToCedarError> {
    conn.query_opt(query_string, &[&uid.id().as_ref()])?
        .map(|row| {
            Ok(ParsedEntity::new(uid.clone(), attrs(&row)?, ancestors(&row)?))
        })
        .transpose()
}
