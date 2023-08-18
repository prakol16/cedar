use std::collections::HashMap;
use cedar_policy::{EntityTypeName, Schema, RandomRequestEnv, ResidualResponse, Effect};
use cedar_policy_core::ast::{Expr, ExprBuilder};
use cedar_policy_validator::{ValidationMode, typecheck::Typechecker};
use smol_str::SmolStr;
use thiserror::Error;

use sea_query::{IntoColumnRef, Alias, IntoIden, Query, SelectStatement, IntoTableRef, TableRef, SeaRc, Iden, SqliteQueryBuilder, PostgresQueryBuilder};

use crate::{query_expr::{ExprWithBindings, QueryExprError, QueryExpr, IdGen}, expr_to_query::InConfig};


/// A wrapper around seaquery's builder with some Cedar-specific additions
#[derive(Debug, Clone, PartialEq)]
pub struct QueryBuilder {
    query: SelectStatement,
    /// Keeps a map of free variables --> (table name, id column name, table added)
    table_names: HashMap<SmolStr, (bool, TableRef, SeaRc<dyn Iden>)>
}

#[derive(Debug, Error)]
pub enum QueryBuilderError {
    #[error("Variable {0} not present or not free in query")]
    UnknownVariable(String),
    #[error("Error occured translating expression to query: {0}")]
    QueryExprError(#[from] QueryExprError),
    #[error("Unknown is not unique")]
    MultipleUnknowns,
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
        let (added, table, _) = self.table_names.get_mut(unknown.into())
            .ok_or_else(|| QueryBuilderError::UnknownVariable(unknown.into()))?;
        if !*added {
            self.query.from_as(table.clone(), Alias::new(unknown));
            *added = true;
            Ok(true)
        } else { Ok(false) }
    }

    fn query_for_id_or_alias(&mut self, unknown: &str, iden: Option<&str>) -> Result<()> {
        let (added, table, id) = self.table_names.get_mut(unknown.into())
            .ok_or_else(|| QueryBuilderError::UnknownVariable(unknown.into()))?;
        if !*added {
            self.query.from_as(table.clone(), Alias::new(unknown));
            *added = true;
        }

        let col = iden.map_or_else(|| id.clone(), |x| Alias::new(x).into_iden());

        self.query.column((Alias::new(unknown), col));
        Ok(())
    }

    /// Add an unknown to the query (i.e. fetching the id of the unknown). This will ensure that the corresponding table is added to the query.
    pub fn query_for(&mut self, unknown: &str) -> Result<()> {
        self.query_for_id_or_alias(unknown, None)
    }

    pub fn query_for_attr(&mut self, unknown: &str, attr: &str) -> Result<()> {
        self.query_for_id_or_alias(unknown, Some(attr))
    }

    pub fn get_unique_unknown(&self) -> Result<SmolStr> {
        let len = self.table_names.len();
        if len == 0 {
            Err(QueryBuilderError::NoEntityTypedUnknown)
        } else if len == 1 {
            Ok(self.table_names.keys().next().unwrap().to_owned())
        } else {
            Err(QueryBuilderError::MultipleUnknowns)
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

    pub fn to_string<T: sea_query::QueryBuilder>(&self, builder: T) -> String {
        self.query.to_string(builder)
    }

    pub fn to_string_sqlite(&self) -> String {
        self.to_string(SqliteQueryBuilder)
    }

    pub fn to_string_postgres(&self) -> String {
        self.to_string(PostgresQueryBuilder)
    }
}

impl ExprWithBindings {
    pub fn to_sql_query<T: IntoTableRef, U: IntoIden>(&self, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<QueryBuilder> {
        let mut query = Query::select();
        query.and_where(self.expr.to_sql_query(&ein)?);
        for (bv, e) in self.bindings.iter() {
            let (tbl_ref, id_name) = table_names(&bv.ty);
            let id_name = id_name.into_iden();
            query.join_as(sea_query::JoinType::InnerJoin,
                tbl_ref, Alias::new(bv.name.clone()),
                e.to_sql_query(&ein)?.eq((Alias::new(bv.name.clone()), id_name).into_column_ref()));
        }

        let mut unk_table_names = HashMap::new();
        let unks = self.get_free_vars();
        for (unk, tp) in unks {
            if let Some(ty) = tp {
                let (tbl_ref, id_name) = table_names(ty);
                unk_table_names.insert(unk.name.clone(), (false, tbl_ref.into_table_ref(), id_name.into_iden()));
            }
        }

        Ok(QueryBuilder { query, table_names: unk_table_names })
    }

    pub fn add_froms<T: IntoTableRef, U: IntoIden>(&self, query: &mut SelectStatement, table_names: impl Fn(&EntityTypeName) -> (T, U)) {
        let unks = self.get_free_vars();
        for (unk, tp) in unks {
            if let Some(ty) = tp {
                let (tbl_ref, _) = table_names(ty);
                query.from_as(tbl_ref, Alias::new(unk.name.as_str()));  // todo: cross join any further tables
            }
        }
    }

    pub fn add_ids<T: IntoTableRef, U: IntoIden>(&self, query: &mut SelectStatement, table_names: impl Fn(&EntityTypeName) -> (T, U)) {
        let unks = self.get_free_vars();
        for (unk, tp) in unks {
            if let Some(ty) = tp {
                let (_, id_name) = table_names(ty);
                query.column((Alias::new(unk.name.as_str()), id_name.into_iden()));
            }
        }
    }
}

/// Does the translation from Cedar to SQL
pub fn translate_expr<T: IntoTableRef, U: IntoIden>(expr: &Expr, schema: &Schema, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<QueryBuilder> {
    let typechecker = Typechecker::new(&schema.0, ValidationMode::Strict);
    let req_env = RandomRequestEnv::new();
    let typed_expr = typechecker.typecheck_expr_strict(&(&req_env).into(), expr, cedar_policy_validator::types::Type::primitive_boolean(), &mut Vec::new())
        .ok_or(QueryExprError::TypecheckError)?;

    let query_expr: QueryExpr = (&typed_expr).try_into()?;

    let mut query_with_bindings: ExprWithBindings = query_expr.into();
    query_with_bindings.reduce_attrs(&mut IdGen::new());

    query_with_bindings.to_sql_query(ein, table_names)
}


pub fn translate_response<T: IntoTableRef, U: IntoIden>(resp: &ResidualResponse, schema: &Schema, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<QueryBuilder> {
    let (permits, forbids): (Vec<_>, Vec<_>) =
        resp.residuals().policies()
            .partition(|p| p.effect() == Effect::Permit);
    let expr: Expr = ExprBuilder::new().and(
        ExprBuilder::new().any(permits.into_iter().map(|p| p.non_head_constraints().clone())),
        ExprBuilder::new().not(ExprBuilder::new().any(forbids.into_iter().map(|p| p.non_head_constraints().clone()))));
    let query = translate_expr(&expr, schema, ein, table_names)?;
    Ok(query)
}

#[cfg(test)]
mod test {
    use cedar_policy::Schema;
    use cedar_policy_core::{evaluator::RestrictedEvaluator, extensions::Extensions, ast};
    use sea_query::Alias;

    use crate::expr_to_query::InByTable;

    use super::translate_expr;

    /// Translation function for the purposes of testing; fills in lots of boilerplate
    pub fn translate_expr_test(expr: ast::Expr, schema: &Schema) -> String {
        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.partial_interpret_unrestricted(&expr, &["unknown".parse().unwrap()].into()).unwrap();

        let mut query = translate_expr(&expr, schema, &InByTable(|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok((Alias::new(in_table), Alias::new(t1_str), Alias::new(t2_str)))
        }), |tp| (Alias::new(tp.basename()), Alias::new("uid"))).unwrap();

        query.query_default().expect("Querying the only unknown should succeed");
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
                        }
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
                        "memberOfTypes": ["Photos"]
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
        "#.parse().unwrap()
    }

    #[test]
    fn test_basic() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos").owner == Users::"0""#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."owner" = '0'"#);
    }

    #[test]
    fn test_entity_deref_id() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos") == Photos::"0""#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."uid" = '0'"#);
    }

    #[test]
    fn test_if() {
        let result = translate_expr_test(
            r#"(if unknown("resource: Photos").owner == Users::"0" then Photos::"beach" else Photos::"carnival") == unknown("resource: Photos").nextPhoto"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE (CASE WHEN ("resource"."owner" = '0') THEN 'beach' ELSE 'carnival' END) = "resource"."nextPhoto""#);
    }

    #[test]
    fn test_nested_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown("resource: Photos").owner.level"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE 5 <= "v__entity_attr_0"."level""#);
    }

    #[test]
    fn test_deeply_nested_getattr() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos").nextPhoto.nextPhoto.nextPhoto.owner.level == 3"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" INNER JOIN "Photos" AS "v__entity_attr_0" ON "resource"."nextPhoto" = "v__entity_attr_0"."uid" INNER JOIN "Photos" AS "v__entity_attr_1" ON "v__entity_attr_0"."nextPhoto" = "v__entity_attr_1"."uid" INNER JOIN "Photos" AS "v__entity_attr_2" ON "v__entity_attr_1"."nextPhoto" = "v__entity_attr_2"."uid" INNER JOIN "Users" AS "v__entity_attr_3" ON "v__entity_attr_2"."owner" = "v__entity_attr_3"."uid" WHERE "v__entity_attr_3"."level" = 3"#);
    }

    #[test]
    fn test_double_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown("resource: Photos").owner.level && unknown("resource: Photos").owner.level <= 10"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE (5 <= "v__entity_attr_0"."level") AND ("v__entity_attr_0"."level" <= 10)"#);
    }

    #[test]
    fn test_if_getattr() {
        let result = translate_expr_test(
            r#"(if unknown("resource: Photos") == Photos::"0" || unknown("resource: Photos") == Photos::"1" then unknown("resource: Photos") else unknown("resource: Photos").nextPhoto).owner == Users::"2""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" INNER JOIN "Photos" AS "v__entity_attr_0" ON (CASE WHEN (("resource"."uid" = '0') OR ("resource"."uid" = '1')) THEN "resource"."uid" ELSE "resource"."nextPhoto" END) = "v__entity_attr_0"."uid" WHERE "v__entity_attr_0"."owner" = '2'"#);
    }

    #[test]
    fn test_in() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos") in Users::"0""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE '0' IN (SELECT "Photos_in_Users"."Users" FROM "Photos_in_Users" WHERE "Photos_in_Users"."Photos" = "resource"."uid")"#);
    }

    #[test]
    fn test_in2() {
        let result: String = translate_expr_test(
            r#"Users::"0" in unknown("resource: Photos")"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" WHERE "resource"."uid" IN (SELECT "Users_in_Photos"."Photos" FROM "Users_in_Photos" WHERE "Users_in_Photos"."Users" = '0')"#);
    }

    #[test]
    fn test_inset() {
        let result: String = translate_expr_test(
            r#"Photos::"0" in unknown("principal: Users").allowedPhotos"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "principal"."uid" FROM "Users" AS "principal" WHERE ('0' = ANY("principal"."allowedPhotos")) OR ('0' IN (SELECT "Photos_in_Photos"."Photos" FROM "Photos_in_Photos" WHERE "Photos_in_Photos"."Photos" = ANY("principal"."allowedPhotos")))"#)
    }

    #[test]
    fn test_record_attr() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos").owner.info.name == "Bob""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE "v__entity_attr_0"."info" ->> 'name' = 'Bob'"#)
    }
}
