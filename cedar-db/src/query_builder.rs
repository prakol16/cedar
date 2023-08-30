use std::collections::HashMap;
use cedar_policy::{EntityTypeName, Schema, RandomRequestEnv, ResidualResponse, Effect};
use cedar_policy_core::ast::{Expr, ExprBuilder};
use cedar_policy_validator::{ValidationMode, typecheck::Typechecker};
use smol_str::SmolStr;
use thiserror::Error;

use sea_query::{IntoColumnRef, Alias, IntoIden, Query, SelectStatement, IntoTableRef, TableRef, SeaRc, Iden, SqliteQueryBuilder, PostgresQueryBuilder};

use crate::{query_expr::{ExprWithBindings, QueryExprError, QueryExpr, UnknownType}, expr_to_query::InConfig};


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
        let (added, table, _) = self.table_names.get_mut(unknown)
            .ok_or_else(|| QueryBuilderError::UnknownVariable(unknown.into()))?;
        if !*added {
            self.query.from_as(table.clone(), Alias::new(unknown));
            *added = true;
            Ok(true)
        } else { Ok(false) }
    }

    fn query_for_id_or_alias(&mut self, unknown: &str, iden: Option<&str>) -> Result<()> {
        let (added, table, id) = self.table_names.get_mut(unknown)
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
            query.join_as(sea_query::JoinType::LeftJoin,
                tbl_ref, Alias::new(bv.name.clone()),
                e.to_sql_query(&ein)?.eq((Alias::new(bv.name.as_str()), id_name).into_column_ref()));
        }

        let mut unk_table_names = HashMap::new();
        let unks = self.get_free_vars();
        for unk in unks {
            if let UnknownType::EntityType { ty, name } = unk {
                let (tbl_ref, id_name) = table_names(ty);
                unk_table_names.insert(name.clone(), (false, tbl_ref.into_table_ref(), id_name.into_iden()));
            }
        }

        Ok(QueryBuilder { query, table_names: unk_table_names })
    }
}


/// Does the translation from Cedar to SQL
pub fn translate_expr_with_renames<T: IntoTableRef, U: IntoIden>(expr: &Expr, schema: &Schema, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U), unknown_map: &HashMap<UnknownType, UnknownType>) -> Result<QueryBuilder> {
    let typechecker = Typechecker::new(&schema.0, ValidationMode::Strict);
    // The request environment should no longer matter, so this is a dirty hack to
    // allocate memory for a request environment that we know will actually never be used.
    let req_env = RandomRequestEnv::new();
    let typed_expr = typechecker.typecheck_expr_strict(&(&req_env).into(), expr, cedar_policy_validator::types::Type::primitive_boolean(), &mut Vec::new())
        .ok_or(QueryExprError::TypecheckError)?;

    let mut query_expr: QueryExpr = (&typed_expr).try_into()?;
    query_expr.rename(unknown_map);

    let mut query_with_bindings: ExprWithBindings = query_expr.into();
    query_with_bindings.reduce_attrs();

    query_with_bindings.to_sql_query(ein, table_names)
}


/// Does the translation from Cedar to SQL
pub fn translate_expr<T: IntoTableRef, U: IntoIden>(expr: &Expr, schema: &Schema, ein: impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<QueryBuilder> {
    translate_expr_with_renames(expr, schema, ein, table_names, &HashMap::new())
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
    use std::collections::HashMap;

    use cedar_policy::Schema;
    use cedar_policy_core::{evaluator::RestrictedEvaluator, extensions::Extensions, ast};
    use sea_query::{Alias, PostgresQueryBuilder};

    use crate::{expr_to_query::InByTable, query_expr::UnknownType};

    use super::{translate_expr, translate_expr_with_renames};

    /// Translation function for the purposes of testing; fills in lots of boilerplate
    pub fn translate_expr_test(expr: ast::Expr, schema: &Schema) -> String {
        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.partial_interpret_unrestricted(&expr, &["unknown".parse().unwrap()].into()).unwrap();

        let mut query = translate_expr(&expr, schema, InByTable(|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok(Some((Alias::new(in_table), Alias::new(t1_str), Alias::new(t2_str))))
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
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE 5 <= "temp__0"."level""#);
    }

    #[test]
    fn test_deeply_nested_getattr() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos").nextPhoto.nextPhoto.nextPhoto.owner.level == 3"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Photos" AS "temp__0" ON "resource"."nextPhoto" = "temp__0"."uid" LEFT JOIN "Photos" AS "temp__1" ON "temp__0"."nextPhoto" = "temp__1"."uid" LEFT JOIN "Photos" AS "temp__2" ON "temp__1"."nextPhoto" = "temp__2"."uid" LEFT JOIN "Users" AS "temp__3" ON "temp__2"."owner" = "temp__3"."uid" WHERE "temp__3"."level" = 3"#);
    }

    #[test]
    fn test_double_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown("resource: Photos").owner.level && unknown("resource: Photos").owner.level <= 10"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE 5 <= "temp__0"."level" AND "temp__0"."level" <= 10"#);
    }

    #[test]
    fn test_if_getattr() {
        let result = translate_expr_test(
            r#"(if unknown("resource: Photos") == Photos::"0" || unknown("resource: Photos") == Photos::"1" then unknown("resource: Photos") else unknown("resource: Photos").nextPhoto).owner == Users::"2""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Photos" AS "temp__0" ON (CASE WHEN ("resource"."uid" = '0' OR "resource"."uid" = '1') THEN "resource"."uid" ELSE "resource"."nextPhoto" END) = "temp__0"."uid" WHERE "temp__0"."owner" = '2'"#);
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
        assert_eq!(result, r#"SELECT "principal"."uid" FROM "Users" AS "principal" WHERE '0' = ANY("principal"."allowedPhotos") OR '0' IN (SELECT "Photos_in_Photos"."Photos" FROM "Photos_in_Photos" WHERE "Photos_in_Photos"."Photos" = ANY("principal"."allowedPhotos"))"#)
    }

    #[test]
    fn test_record_attr() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos").owner.info.name == "Bob""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "resource"."uid" FROM "Photos" AS "resource" LEFT JOIN "Users" AS "temp__0" ON "resource"."owner" = "temp__0"."uid" WHERE ("temp__0"."info" ->> 'name') = 'Bob'"#)
    }

    #[test]
    fn test_rename() {
        let expr: ast::Expr = r#"unknown("resource: Photos").owner == Users::"bob""#.parse().unwrap();

        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.partial_interpret_unrestricted(&expr, &["unknown".parse().unwrap()].into()).unwrap();

        let mut query = translate_expr_with_renames(&expr, &get_schema(), InByTable(|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok(Some((Alias::new(in_table), Alias::new(t1_str), Alias::new(t2_str))))
        }), |tp| (Alias::new(tp.basename()), Alias::new("uid")),
    &HashMap::from([
            (UnknownType::EntityType { ty: "Photos".parse().unwrap(), name: "resource".into() },
            UnknownType::EntityType { ty: "Photos".parse().unwrap(), name: "pictures".into() }),
        ])).unwrap();

        query.query_default().expect("Querying the only unknown should succeed");
        assert_eq!(query.to_string_postgres(), r#"SELECT "pictures"."uid" FROM "Photos" AS "pictures" WHERE "pictures"."owner" = 'bob'"#);
    }

    #[test]
    fn test_name_collision() {
        let result = translate_expr_test(
            r#"5 <= unknown("temp__0: Photos").owner.level"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT "temp__0"."uid" FROM "Photos" AS "temp__0" LEFT JOIN "Users" AS "temp__1" ON "temp__0"."owner" = "temp__1"."uid" WHERE 5 <= "temp__1"."level""#);
    }

    #[test]
    fn test_build() {
        let expr = r#"10 * unknown("user: Users").level + unknown("user: Users").info.age >= 50"#.parse().unwrap();
        let schema = &get_schema();

        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.partial_interpret_unrestricted(&expr, &["unknown".parse().unwrap()].into()).unwrap();

        let mut query = translate_expr(&expr, schema, InByTable(|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok(Some((Alias::new(in_table), Alias::new(t1_str), Alias::new(t2_str))))
        }), |tp| (Alias::new(tp.basename()), Alias::new("uid"))).unwrap();

        query.query_default().expect("Querying the only unknown should succeed");

        let (result, values) = query.into_select_statement().build(PostgresQueryBuilder);
        assert_eq!(result, r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE $1 <= ("user"."level" * $2) + CAST(("user"."info" -> $3) AS integer)"#);
        assert_eq!(values.0, vec![50i64.into(), 10i64.into(), "age".into()]);
    }

    #[test]
    fn test_json_array_cast() {
        let result = translate_expr_test(
            r#"unknown("user: Users").info.setAttr.containsAll([6, 10, 11])"#.parse().unwrap(),
            &get_schema()
        );
        println!("{}", result);
        assert_eq!(result, r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result")) @> (ARRAY[6, 10, 11])"#)
    }

    #[test]
    fn test_json_array_eq() {
        let result = translate_expr_test(
            r#"unknown("user: Users").info.setAttr == [6, 10, 11]"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT "user"."uid" FROM "Users" AS "user" WHERE Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result")) @> (ARRAY[6, 10, 11]) AND (ARRAY[6, 10, 11]) @> Array((SELECT CAST("result"."value" AS integer) FROM jsonb_array_elements("user"."info" -> 'setAttr') AS "result"))"#);
    }
}
