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

//! Integration between Postgresql and Cedar entity stores

use std::collections::{HashMap, HashSet};

use cedar_policy::{
    EntityAttrAccessError, EntityId, EntityTypeName, EntityUid, ParsedEntity, PartialValue, Value,
};
use postgres::{
    types::{FromSql, FromSqlOwned, Kind, Type},
    Client, Row,
};
use sea_query::{PostgresQueryBuilder, SelectStatement};
use smol_str::SmolStr;

use crate::sql_common::{
    make_ancestors, AncestorSQLInfo, DatabaseToCedarError, EntitySQLId, EntitySQLInfo,
    IsSQLDatabase, SQLValue,
};

impl<'a> FromSql<'a> for SQLValue {
    fn from_sql(
        ty: &Type,
        raw: &'a [u8],
    ) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
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
            Ok(
                <HashMap<String, Option<String>> as FromSql>::from_sql(ty, raw)?
                    .into_iter()
                    .filter_map(|(k, v)| Some((k, v?.into())))
                    .collect::<Vec<(String, Value)>>()
                    .into(),
            )
        } else if let Kind::Array(_) = ty.kind() {
            Ok(<Vec<SQLValue> as FromSql>::from_sql(ty, raw)?
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

    fn from_sql_null(_: &Type) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        Ok(SQLValue(None))
    }

    fn accepts(ty: &postgres::types::Type) -> bool {
        bool::accepts(ty)
            || i32::accepts(ty)
            || i64::accepts(ty)
            || u32::accepts(ty)
            || String::accepts(ty)
            || <HashMap<String, Option<String>> as FromSql>::accepts(ty)
            || (match ty.kind() {
                Kind::Array(inner) => <SQLValue as FromSql>::accepts(inner),
                _ => false,
            })
            || <serde_json::Value as FromSql>::accepts(ty)
    }
}

impl<'a> FromSql<'a> for EntitySQLId {
    fn from_sql(
        ty: &Type,
        raw: &'a [u8],
    ) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
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

/// Postgres-specific SQL info
#[allow(missing_debug_implementations)]
pub struct PostgresSQLInfo;

impl IsSQLDatabase for PostgresSQLInfo {}

impl EntitySQLInfo<PostgresSQLInfo> {
    /// Get all ancestors of an entity when the ancestors are stored in a column of the entity table
    pub fn make_entity_ancestors(
        &self,
        conn: &mut Client,
        uid: &EntityUid,
    ) -> Result<Option<ParsedEntity>, DatabaseToCedarError> {
        self.make_entity(conn, uid, |row| match self.ancestor_attr_ind {
            Some(ancestors_attr_ind) => make_ancestors(row.get(ancestors_attr_ind)),
            None => panic!(
                "make_entity_ancestors should only be called when `ancestors_attr_ind` is filled"
            ),
        })
    }

    /// Get entity given a function which determines how to get ancestors given the information in the row
    pub fn make_entity(
        &self,
        conn: &mut Client,
        uid: &EntityUid,
        ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, DatabaseToCedarError>,
    ) -> Result<Option<ParsedEntity>, DatabaseToCedarError> {
        Self::make_entity_from_table(
            conn,
            uid,
            &self.get_select(uid.id()),
            |row| Self::convert_attr_names(&row, &self.attr_names_map),
            ancestors,
        )
    }

    /// Create an entity using `make_entity` and supply extra attributes that can depend on the row
    /// Useful for when some attributes are nontrivial functions of the data stored in the table
    pub fn make_entity_extra_attrs(
        &self,
        conn: &mut Client,
        uid: &EntityUid,
        ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, DatabaseToCedarError>,
        extra_attrs: impl FnOnce(&Row) -> Result<HashMap<String, PartialValue>, DatabaseToCedarError>,
    ) -> Result<Option<ParsedEntity>, DatabaseToCedarError> {
        Self::make_entity_from_table(
            conn,
            uid,
            &self.get_select(uid.id()),
            |row| {
                let mut attrs = Self::convert_attr_names(&row, &self.attr_names_map)?;
                attrs.extend(extra_attrs(row)?);
                Ok(attrs)
            },
            ancestors,
        )
    }

    /// Get a single attribute of an entity
    pub fn get_single_attr_as<'a, T: FromSqlOwned>(
        &self,
        conn: &mut Client,
        id: &EntityId,
        attr: &str,
    ) -> Result<T, EntityAttrAccessError<DatabaseToCedarError>> {
        let query = self
            .get_single_attr_select(id, attr)
            .ok_or(EntityAttrAccessError::UnknownAttr)?;
        let query_result: T = conn
            .query_opt(&query.to_string(PostgresQueryBuilder), &[])
            .map_err(DatabaseToCedarError::from)?
            .ok_or(EntityAttrAccessError::UnknownEntity)?
            .get(0);
        Ok(query_result)
    }

    /// Get a single attribute of an entity as a cedar `Value`
    pub fn get_single_attr(
        &self,
        conn: &mut Client,
        id: &EntityId,
        attr: &str,
    ) -> Result<Value, EntityAttrAccessError<DatabaseToCedarError>> {
        let query_result: SQLValue = self.get_single_attr_as(conn, id, attr)?;
        match query_result {
            SQLValue(Some(v)) => Ok(v),
            SQLValue(None) => Err(EntityAttrAccessError::UnknownAttr),
        }
    }

    /// Get a single attribute of an entity as a cedar `EntityUid`
    pub fn get_single_attr_as_id(
        &self,
        conn: &mut Client,
        id: &EntityId,
        attr: &str,
        tp: EntityTypeName,
    ) -> Result<EntityUid, EntityAttrAccessError<DatabaseToCedarError>> {
        let query_result: EntitySQLId = self.get_single_attr_as(conn, id, attr)?;
        Ok(query_result.into_uid(tp))
    }

    /// Check whether the given entity exists
    pub fn exists_entity(
        &self,
        conn: &mut Client,
        id: &EntityId,
    ) -> Result<bool, DatabaseToCedarError> {
        let query = self.get_exists_select(id);
        Ok(conn
            .query_opt(&query.to_string(PostgresQueryBuilder), &[])?
            .is_some())
    }

    /// Convert a row into a map of attribute names to values
    pub fn convert_attr_names(
        query_result: &Row,
        attr_names: &HashMap<SmolStr, usize>,
    ) -> Result<HashMap<String, PartialValue>, DatabaseToCedarError> {
        attr_names
            .iter()
            .filter_map(|(nm, ind)| match query_result.get::<_, SQLValue>(*ind) {
                SQLValue(Some(v)) => Some(Ok((nm.to_string(), v.into()))),
                SQLValue(None) => None,
            })
            .collect()
    }

    /// Construct an entity from a row in the entity table given a
    /// function which determines how to get ancestors given the information in the row
    /// and how to get attributes given the information in the row
    pub fn make_entity_from_table(
        conn: &mut Client,
        uid: &EntityUid,
        query: &SelectStatement,
        attrs: impl FnOnce(&Row) -> Result<HashMap<String, PartialValue>, DatabaseToCedarError>,
        ancestors: impl FnOnce(&Row) -> Result<HashSet<EntityUid>, DatabaseToCedarError>,
    ) -> Result<Option<ParsedEntity>, DatabaseToCedarError> {
        // TODO: use `build` instead of `to_string`
        let query_string = query.to_string(PostgresQueryBuilder);
        conn.query_opt(&query_string, &[])?
            .map(|row| {
                Ok(ParsedEntity::new(
                    uid.clone(),
                    attrs(&row)?,
                    ancestors(&row)?,
                ))
            })
            .transpose()
    }
}

impl AncestorSQLInfo<PostgresSQLInfo> {
    /// Get all ancestors of an entity when the ancestry information is stored in a separate table
    pub fn get_ancestors(
        &self,
        conn: &mut Client,
        id: &EntityId,
        tp: &EntityTypeName,
    ) -> Result<HashSet<EntityUid>, DatabaseToCedarError> {
        Ok(conn
            .query(
                &self.query_all_parents(id).to_string(PostgresQueryBuilder),
                &[],
            )?
            .into_iter()
            .map(|row| {
                let parent_id: EntitySQLId = row.get(0);
                parent_id.into_uid(tp.clone())
            })
            .collect())
    }

    /// Check whether the given entity is a descendant of the given entity
    pub fn is_ancestor(
        &self,
        conn: &mut Client,
        child_id: &EntityId,
        parent_id: &EntityId,
    ) -> Result<bool, DatabaseToCedarError> {
        Ok(conn
            .query_opt(
                &self
                    .query_is_parent(child_id, parent_id)
                    .to_string(PostgresQueryBuilder),
                &[],
            )?
            .is_some())
    }
}
