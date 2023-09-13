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

//! Customizer for queries -- can customize the tables and the columns that are queried
use cedar_policy::{Effect, EntityTypeName, RandomRequestEnv, ResidualResponse, Schema};
use cedar_policy_core::{
    ast::{Expr, ExprBuilder},
    authorizer::PartialResponse,
};
use cedar_policy_validator::{typecheck::Typechecker, ValidationMode};
use smol_str::SmolStr;
use std::collections::HashMap;
use thiserror::Error;

use sea_query::{
    Alias, IntoColumnRef, IntoTableRef, PostgresQueryBuilder, Query, SelectStatement,
    SqliteQueryBuilder, TableRef,
};

use crate::{
    expr_to_query::InConfig,
    query_expr::{ExprWithBindings, QueryExprError, QueryExprWithVars, UnknownType},
};

/// A wrapper around seaquery's builder with some Cedar-specific additions
#[derive(Debug, Clone, PartialEq)]
pub struct QueryBuilder {
    query: SelectStatement,
    /// Keeps a map of free variables --> (table added?, table name, id column name)
    table_names: HashMap<SmolStr, (bool, TableRef, SmolStr)>,
}

/// Error that can occur when building a query
#[derive(Debug, Error)]
pub enum QueryBuilderError {
    /// Occurs when query_for is called on a variable that is not present in the query
    #[error("Variable {0} not present or not free in query")]
    UnknownVariable(String),

    /// Occurs when the query expression cannot be translated to a query
    #[error("Error occured translating expression to query: {0}")]
    QueryExprError(#[from] QueryExprError),

    /// Occurs when there are multiple unknowns in the query and query_default() is called
    #[error("Unknown is not unique")]
    MultipleUnknowns,

    /// Occurs when there are no unknowns in the query and query_default() is called
    #[error("No entity typed unknown in query; build the query manually")]
    NoEntityTypedUnknown,
}

type Result<T> = std::result::Result<T, QueryBuilderError>;

impl QueryBuilder {
    /// Get the select sea query statement -- allows more fine grained control of the resulting query
    pub fn get_select_statement(&self) -> &SelectStatement {
        &self.query
    }

    /// Take ownership of the select sea query statement -- allows more fine grained control of the resulting query
    pub fn into_select_statement(self) -> SelectStatement {
        self.query
    }

    /// Add an unknown to the query as a table. Note that this does not add the id column to the query.
    pub fn query_table(&mut self, unknown: &str) -> Result<bool> {
        let (added, table, _) = self
            .table_names
            .get_mut(unknown)
            .ok_or_else(|| QueryBuilderError::UnknownVariable(unknown.into()))?;
        if !*added {
            self.query.from_as(table.clone(), Alias::new(unknown));
            *added = true;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn query_for_id_or_alias(&mut self, unknown: &str, iden: Option<&str>) -> Result<()> {
        let (added, table, id) = self
            .table_names
            .get_mut(unknown)
            .ok_or_else(|| QueryBuilderError::UnknownVariable(unknown.into()))?;
        if !*added {
            self.query.from_as(table.clone(), Alias::new(unknown));
            *added = true;
        }

        let col = iden.unwrap_or(id.as_str());

        self.query.column((Alias::new(unknown), Alias::new(col)));
        Ok(())
    }

    /// Add an unknown to the query (i.e. fetching the id of the unknown). This will ensure that the corresponding table is added to the query.
    pub fn query_for(&mut self, unknown: &str) -> Result<()> {
        self.query_for_id_or_alias(unknown, None)
    }

    /// Add an unknown to the query with the given attribute rather than the id. This will ensure that the corresponding table is added to the query.
    pub fn query_for_attr(&mut self, unknown: &str, attr: &str) -> Result<()> {
        self.query_for_id_or_alias(unknown, Some(attr))
    }

    /// Get the only unknown in the query. If there are multiple or no unknowns, this will return an error.
    pub fn get_unique_unknown(&self) -> Result<SmolStr> {
        let len = self.table_names.len();
        if len > 1 {
            Err(QueryBuilderError::MultipleUnknowns)
        } else {
            Ok(self
                .table_names
                .keys()
                .next()
                .ok_or(QueryBuilderError::NoEntityTypedUnknown)?
                .to_owned())
        }
    }

    /// Query for the id of the only (entity-typed) unknown in the query.
    pub fn query_default(&mut self) -> Result<()> {
        let unknown = self.get_unique_unknown()?;
        self.query_for(unknown.as_str())
    }

    /// Query for the attribute of the only (entity-typed) unknown in the query.
    pub fn query_default_attr(&mut self, attr: &str) -> Result<()> {
        let unknown = self.get_unique_unknown()?;
        self.query_for_attr(unknown.as_str(), attr)
    }

    /// Get the query as a string
    pub fn to_string<T: sea_query::QueryBuilder>(&self, builder: T) -> String {
        self.query.to_string(builder)
    }

    /// Get the query as a SQLite query
    /// TODO: Use build() instead
    pub fn to_string_sqlite(&self) -> String {
        self.to_string(SqliteQueryBuilder)
    }

    /// Get the query as a Postgres query
    /// TODO: Use build() instead
    pub fn to_string_postgres(&self) -> String {
        self.to_string(PostgresQueryBuilder)
    }
}

impl ExprWithBindings {
    /// Given a query, add the left joins for the bindings in this ExprWithQuery
    fn join_bindings<T: IntoTableRef>(&self, query: &mut SelectStatement, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, SmolStr)) -> Result<()> {
        for (bv, e) in self.bindings.iter() {
            let (tbl_ref, id_name) = table_names(&bv.ty);
            let id_name = Alias::new(id_name);
            query.join_as(
                sea_query::JoinType::LeftJoin,
                tbl_ref,
                Alias::new(bv.name.clone()),
                e.to_sql_query(&ein)?
                    .eq((Alias::new(bv.name.as_str()), id_name).into_column_ref()),
            );
        }
        Ok(())
    }

    /// Convert the given expression to a select statement with joins that selects the result of the
    /// expression
    pub fn to_sql_expr_query<T: IntoTableRef>(
        &self,
        ein: impl InConfig,
        table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
    ) -> Result<SelectStatement> {
        let mut query = Query::select();
        query.expr(self.expr.to_sql_query(&ein)?);
        self.join_bindings(&mut query, ein, table_names)?;
        Ok(query)
    }

    /// Convert the given expression to a QueryBuilder which has the inner joins filled in
    /// All that is left to fill is the table name and column names that will be fetched
    pub fn to_sql_query<T: IntoTableRef>(
        &self,
        ein: impl InConfig,
        table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
    ) -> Result<QueryBuilder> {
        let mut query = Query::select();
        query.and_where(self.expr.to_sql_query(&ein)?);
        self.join_bindings(&mut query, ein, &table_names)?;

        // We collect all the free unknowns that have entity type so that the
        // query builder knows which tables to add when certain variables are requested
        let mut unk_table_names = HashMap::new();
        let unks = self.get_free_vars();
        for unk in unks {
            if let UnknownType::EntityType { ty, name } = unk {
                let (tbl_ref, id_name) = table_names(ty);
                unk_table_names.insert(name.clone(), (false, tbl_ref.into_table_ref(), id_name));
            }
        }

        Ok(QueryBuilder {
            query,
            table_names: unk_table_names,
        })
    }
}

/// Does translation from Cedar to ExprWithBindings, which
/// the user can then do further transformations on
pub fn translate_expr_to_expr_with_bindings<T: IntoTableRef>(
    expr: &Expr,
    schema: &Schema,
    table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
    unknown_map: &HashMap<UnknownType, UnknownType>,
) -> Result<ExprWithBindings> {
    // Get the free variables in the original expression
    let vars = expr
        .subexpressions()
        .filter_map(UnknownType::from_expr)
        .collect::<Vec<_>>();

    let typechecker = Typechecker::new(&schema.0, ValidationMode::Strict);
    // The request environment should no longer matter, so this is a dirty hack to
    // allocate memory for a request environment that we know will actually never be used.
    let req_env = RandomRequestEnv::new();
    let mut errors = Vec::new();
    let typed_expr = typechecker
        .typecheck_expr_strict(&(&req_env).into(), expr, &mut errors)
        .ok_or_else(|| QueryExprError::ValidationError(errors))?;
    let mut query_expr = QueryExprWithVars::from_expr(&typed_expr, vars)?;
    // Rename any unknowns that appear in the query
    if !unknown_map.is_empty() {
        query_expr.rename(|u| {
            if let Some(new_u) = unknown_map.get(u) {
                *u = new_u.clone();
            }
        });
    }
    // Rename any ids that appear in the query
    query_expr.rename_attrs(|tp, attr| match attr {
        crate::query_expr::AttrOrId::Attr(_) => (),
        crate::query_expr::AttrOrId::Id(s) => *s = table_names(tp).1,
    });

    let mut query_with_bindings: ExprWithBindings = query_expr.into();
    query_with_bindings.reduce_attrs();
    Ok(query_with_bindings)
}

/// Does the translation from Cedar to SQL
pub fn translate_expr_with_renames<T: IntoTableRef>(
    expr: &Expr,
    schema: &Schema,
    ein: impl InConfig,
    table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
    unknown_map: &HashMap<UnknownType, UnknownType>,
) -> Result<QueryBuilder> {
    translate_expr_to_expr_with_bindings(expr, schema, &table_names, unknown_map)?
        .to_sql_query(ein, table_names)
}

/// Does the translation from Cedar to SQL
pub fn translate_expr<T: IntoTableRef>(
    expr: &Expr,
    schema: &Schema,
    ein: impl InConfig,
    table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
) -> Result<QueryBuilder> {
    translate_expr_with_renames(expr, schema, ein, table_names, &HashMap::new())
}

/// Given a residual response `resp`, which will contain unknowns to be filled in
/// return a QueryBuilder containing the query that will fetch the ids of the unknowns
/// The QueryBuilder initially does not have a table filled in, but if there is only one unknown
/// the table can be filled using query_default() (see QueryBuilder for more details)
pub fn translate_response<T: IntoTableRef>(
    resp: &ResidualResponse,
    schema: &Schema,
    ein: impl InConfig,
    table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
) -> Result<QueryBuilder> {
    let (permits, forbids): (Vec<_>, Vec<_>) = resp
        .residuals()
        .policies()
        .partition(|p| p.effect() == Effect::Permit);
    let expr: Expr = ExprBuilder::new().and(
        // In a residual response, all policies have no head constraints (everything is in the non-head constraint)
        ExprBuilder::new().any(
            permits
                .into_iter()
                .map(|p| p.non_head_constraints().clone()),
        ),
        ExprBuilder::new().not(
            ExprBuilder::new().any(
                forbids
                    .into_iter()
                    .map(|p| p.non_head_constraints().clone()),
            ),
        ),
    );
    let query = translate_expr(&expr, schema, ein, table_names)?;
    Ok(query)
}

/// Same as translate_response but uses the core type response
/// TODO: remove (we only use this currently in DRT)
pub fn translate_response_core<T: IntoTableRef>(
    resp: &PartialResponse,
    schema: &Schema,
    ein: impl InConfig,
    table_names: impl Fn(&EntityTypeName) -> (T, SmolStr),
) -> Result<QueryBuilder> {
    let (permits, forbids): (Vec<_>, Vec<_>) = resp
        .residuals
        .policies()
        .partition(|p| p.effect() == Effect::Permit);
    let expr: Expr = ExprBuilder::new().and(
        // In a residual response, all policies have no head constraints (everything is in the non-head constraint)
        ExprBuilder::new().any(
            permits
                .into_iter()
                .map(|p| p.non_head_constraints().clone()),
        ),
        ExprBuilder::new().not(
            ExprBuilder::new().any(
                forbids
                    .into_iter()
                    .map(|p| p.non_head_constraints().clone()),
            ),
        ),
    );
    let query = translate_expr(&expr, schema, ein, &table_names)?;
    Ok(query)
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use cedar_policy::Schema;
    use cedar_policy_core::{
        ast::{self},
        evaluator::RestrictedEvaluator,
        extensions::Extensions,
    };
    use sea_query::{Alias, PostgresQueryBuilder};

    use crate::{expr_to_query::{InByTable, InConfig}, query_expr::UnknownType};

    use super::{translate_expr, translate_expr_with_renames};

    pub fn get_inconfig() -> impl InConfig {
        InByTable(|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok(Some((
                Alias::new(in_table),
                Alias::new(t1_str),
                Alias::new(t2_str),
            )))
        })
    }

    /// Translation function for the purposes of testing; fills in lots of boilerplate
    pub fn translate_expr_test(expr: ast::Expr, schema: &Schema) -> String {
        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.interpret_unknowns(&expr).unwrap();

        let mut query = translate_expr(
            &expr,
            schema,
            get_inconfig(),
            |tp| (Alias::new(tp.basename()), "uid".into()),
        )
        .unwrap();

        query
            .query_default()
            .expect("Querying the only unknown should succeed");
        query.to_string_postgres()
    }

    fn get_schema() -> Schema {
        r#"
        {
            "": {
                "entityTypes": {
                    "Users": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "level": {
                                    "type": "Long"
                                },
                                "info": {
                                    "type": "Record",
                                    "attributes": {
                                        "name": {
                                            "type": "String"
                                        },
                                        "age": {
                                            "type": "Long"
                                        },
                                        "setAttr": {
                                            "type": "Set",
                                            "element": {
                                                "type": "Long"
                                            }
                                        }
                                    }
                                },
                                "allowedPhotos": {
                                    "type": "Set",
                                    "element": {
                                        "type": "Entity",
                                        "name": "Photos"
                                    }
                                }
                            }
                        },
                        "memberOfTypes": ["Photos"]
                    },
                    "Photos": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "owner": {
                                    "type": "Entity",
                                    "name": "Users"
                                },
                                "nextPhoto": {
                                    "type": "Entity",
                                    "name": "Photos"
                                }
                            }
                        },
                        "memberOfTypes": ["Photos", "Users"]
                    }
                },
                "actions": {
                    "view": {
                        "appliesTo": {
                            "principalTypes": ["Users"],
                            "resourceTypes": ["Photos"]
                        }
                    }
                }
            }
        }
        "#
        .parse()
        .unwrap()
    }

    #[test]
    fn test_basic() {
        let result = translate_expr_test(
            r#"unknown::entity("resource", "Photos").owner == Users::"0""#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."owner" = '0'"#
        );
    }

    #[test]
    fn test_entity_deref_id() {
        let result = translate_expr_test(
            r#"unknown::entity("resource", "Photos") == Photos::"0""#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."uid" = '0'"#
        );
    }

    #[test]
    fn test_if() {
        let result = translate_expr_test(
            r#"(if unknown::entity("resource", "Photos").owner == Users::"0" then Photos::"beach" else Photos::"carnival") == unknown::entity("resource", "Photos").nextPhoto"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE (CASE WHEN ("resource"."owner" = '0') THEN 'beach' ELSE 'carnival' END) = "resource"."nextPhoto""#
        );
    }

    #[test]
    fn test_nested_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown::entity("resource", "Photos").owner.level"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE 5 <= "temp__0"."level""#
        );
    }

    #[test]
    fn test_deeply_nested_getattr() {
        let result = translate_expr_test(
            r#"unknown::entity("resource", "Photos").nextPhoto.nextPhoto.nextPhoto.owner.level == 3"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Photos" AS "temp__0" ON "resource"."nextPhoto" = "temp__0"."uid" LEFT JOIN "Photos" AS "temp__1" ON "temp__0"."nextPhoto" = "temp__1"."uid" LEFT JOIN "Photos" AS "temp__2" ON "temp__1"."nextPhoto" = "temp__2"."uid" LEFT JOIN "Users" AS "temp__3" ON "temp__2"."owner" = "temp__3"."uid" WHERE "temp__3"."level" = 3"#
        );
    }

    #[test]
    fn test_double_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown::entity("resource", "Photos").owner.level && unknown::entity("resource", "Photos").owner.level <= 10"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE 5 <= "temp__0"."level" AND "temp__0"."level" <= 10"#
        );
    }

    #[test]
    fn test_if_getattr() {
        let result = translate_expr_test(
            r#"(if unknown::entity("resource", "Photos") == Photos::"0" || unknown::entity("resource", "Photos") == Photos::"1" then unknown::entity("resource", "Photos") else unknown::entity("resource", "Photos").nextPhoto).owner == Users::"2""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Photos" AS "temp__0" ON (CASE WHEN ("resource"."uid" = '0' OR "resource"."uid" = '1') THEN "resource"."uid" ELSE "resource"."nextPhoto" END) = "temp__0"."uid" WHERE "temp__0"."owner" = '2'"#
        );
    }

    #[test]
    fn test_in() {
        let result: String = translate_expr_test(
            r#"unknown::entity("resource", "Photos") in Users::"0""#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE '0' IN (SELECT "Photos_in_Users"."Users" FROM "Photos_in_Users" WHERE "Photos_in_Users"."Photos" = "resource"."uid")"#
        );
    }

    #[test]
    fn test_in2() {
        let result: String = translate_expr_test(
            r#"Users::"0" in unknown::entity("resource", "Photos")"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."uid" IN (SELECT "Users_in_Photos"."Photos" FROM "Users_in_Photos" WHERE "Users_in_Photos"."Users" = '0')"#
        );
    }

    #[test]
    fn test_inset() {
        let result: String = translate_expr_test(
            r#"Photos::"0" in unknown::entity("principal", "Users").allowedPhotos"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "principal"."uid" FROM "Users" AS "principal" WHERE '0' = ANY("principal"."allowedPhotos") OR '0' IN (SELECT "Photos_in_Photos"."Photos" FROM "Photos_in_Photos" WHERE "Photos_in_Photos"."Photos" = ANY("principal"."allowedPhotos"))"#
        )
    }

    #[test]
    fn test_record_attr() {
        let result: String = translate_expr_test(
            r#"unknown::entity("resource", "Photos").owner.info.name == "Bob""#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE ("temp__0"."info" ->> 'name') = 'Bob'"#
        )
    }

    #[test]
    fn test_rename() {
        let expr: ast::Expr = r#"unknown::entity("resource", "Photos").owner == Users::"bob""#
            .parse()
            .unwrap();

        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.interpret_unknowns(&expr).unwrap();

        let mut query = translate_expr_with_renames(
            &expr,
            &get_schema(),
            get_inconfig(),
            |tp| (Alias::new(tp.basename()), "uid".into()),
            &HashMap::from([(
                UnknownType::EntityType {
                    ty: "Photos".parse().unwrap(),
                    name: "resource".into(),
                },
                UnknownType::EntityType {
                    ty: "Photos".parse().unwrap(),
                    name: "pictures".into(),
                },
            )]),
        )
        .unwrap();

        query
            .query_default()
            .expect("Querying the only unknown should succeed");
        assert_eq!(
            query.to_string_postgres(),
            r#"SELECT "pictures"."uid" FROM "Photos" AS "pictures" WHERE "pictures"."owner" = 'bob'"#
        );
    }

    #[test]
    fn test_name_collision() {
        let result = translate_expr_test(
            r#"5 <= unknown::entity("temp__0", "Photos").owner.level"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "temp__0"."uid" FROM "Photos" AS "temp__0" LEFT JOIN "Users" AS "temp__1" ON "temp__0"."owner" = "temp__1"."uid" WHERE 5 <= "temp__1"."level""#
        );
    }

    #[test]
    fn test_build() {
        let expr = r#"10 * unknown::entity("user", "Users").level + unknown::entity("user", "Users").info.age >= 50"#
            .parse()
            .unwrap();
        let schema = &get_schema();

        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.interpret_unknowns(&expr).unwrap();

        let mut query = translate_expr(
            &expr,
            schema,
            get_inconfig(),
            |tp| (Alias::new(tp.basename()), "uid".into()),
        )
        .unwrap();

        query
            .query_default()
            .expect("Querying the only unknown should succeed");

        let (result, values) = query.into_select_statement().build(PostgresQueryBuilder);
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE $1 <= ("user"."level" * $2) + CAST(("user"."info" -> $3) AS integer)"#
        );
        assert_eq!(values.0, vec![50i64.into(), 10i64.into(), "age".into()]);
    }

    #[test]
    fn test_json_array_cast() {
        let result = translate_expr_test(
            r#"unknown::entity("user", "Users").info.setAttr.containsAll([6, 10, 11])"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        println!("{}", result);
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result")) @> (ARRAY[6, 10, 11])"#
        )
    }

    #[test]
    fn test_json_array_eq() {
        let result = translate_expr_test(
            r#"unknown::entity("user", "Users").info.setAttr == [6, 10, 11]"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result")) @> (ARRAY[6, 10, 11]) AND (ARRAY[6, 10, 11]) @> Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result"))"#
        );
    }

    #[test]
    fn test_rawsql() {
        let result = translate_expr_test(
            r#"unknown::entity("user", "Users").level >= rawsql::long(unknown::long("__RAWSQL"), "SELECT AVG(level) FROM Users")"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE (SELECT AVG(level) FROM Users) <= "user"."level""#
        );
    }

    #[test]
    fn test_rawsql_with_params() {
        let result = translate_expr_test(
            r#"unknown::entity("user", "Users").level >= rawsql::long(unknown::long("__RAWSQL"), "SELECT (AVG(level) * $) FROM Users", unknown::entity("user", "Users").info.age)"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE (SELECT (AVG(level) * CAST(("user"."info" -> 'age') AS integer)) FROM Users) <= "user"."level""#
        );
    }

    #[test]
    fn test_escape_sub_char() {
        let result = translate_expr_test(
            r#"unknown::entity("user", "Users") == Users::"""#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE "user"."uid" = ''"#
        );
    }

    #[test]
    fn test_free_vars_in_and_false() {
        let result = translate_expr_test(
            // This expression gets reduced to `false` during strict typechecking
            r#"unknown::entity("user", "Users") == Users::"0" && false"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(
            result,
            r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE "user"."uid" = '0' AND FALSE"#
        );
    }

    #[test]
    fn test_and_false_typeerror() {
        let result = translate_expr_test(
            // The RHS of the and does not typecheck so it should be eliminated
            r#"(unknown::entity("resource", "Photos") == Photos::"0") && (false && ("hello" + 5 == "world"))"#
                .parse()
                .unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."uid" = '0' AND FALSE"#);
    }
}
