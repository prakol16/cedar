use cedar_policy::{EntityTypeName, Schema, RandomRequestEnv, ResidualResponse, Effect};
use cedar_policy_core::ast::{Literal, UnaryOp, BinaryOp, Expr, ExprBuilder};
use cedar_policy_validator::{typecheck::Typechecker, ValidationMode};
use sea_query::{SimpleExpr, IntoColumnRef, BinOper, extension::postgres::{PgBinOper, PgExpr}, Alias, IntoIden, Query, Keyword, PgFunc, SelectStatement};
use smol_str::SmolStr;
use thiserror::Error;

use crate::query_expr::{QueryExprError, QueryExpr, UnknownType, CastableType, ExprWithBindings, OtherUnknown, IdGen};

#[derive(Debug, Error)]
pub enum ExprToSqlError {
    #[error("some error occured: {0}")]
    StringError(String),
}

type Result<T> = std::result::Result<T, QueryExprError>;


fn cedar_binary_to_sql_binary(op: BinaryOp) -> Option<BinOper> {
    match op {
        BinaryOp::Eq => Some(BinOper::Equal),
        BinaryOp::Less => Some(BinOper::SmallerThan),
        BinaryOp::LessEq => Some(BinOper::SmallerThanOrEqual),
        BinaryOp::Add => Some(BinOper::Add),
        BinaryOp::Sub => Some(BinOper::Sub),
        BinaryOp::In => None,
        BinaryOp::Contains => None,
        BinaryOp::ContainsAll => Some(BinOper::PgOperator(PgBinOper::Contains)),
        BinaryOp::ContainsAny => Some(BinOper::PgOperator(PgBinOper::Overlap)),
    }
}

impl IntoColumnRef for OtherUnknown {
    fn into_column_ref(self) -> sea_query::ColumnRef {
        match self.pfx {
            Some(pfx) => (Alias::new(pfx), Alias::new(self.name)).into_column_ref(),
            None => Alias::new(self.name).into_column_ref(),
        }
    }
}

impl QueryExpr {
    fn lit_to_sql(l: &Literal) -> SimpleExpr {
        match l {
            Literal::Bool(b) => (*b).into(),
            Literal::Long(i) => (*i).into(),
            Literal::String(s) => s.as_str().into(),
            Literal::EntityUID(e) => {
                let e_id: &str = e.eid().as_ref();
                e_id.into()
            },
        }
    }

    /// Semantics:
    /// Let phi: Value -> SQLValue be a function which interprets Cedar types as SQL types.
    /// We say (e: Value) corresponds to (e' SQLValue) (i.e. e ~ e') if e = phi(e')
    /// Note that phi is not injective, since entity types are ignored i.e. phi('Users::"1"' : EntityUID) = phi('Teams::"1"' : EntityUID)
    /// Note that we assume array and json extensions to SQL, but only for Record and Set types,
    /// We have: phi(Lit(x: bool | long | string)) = x
    ///          phi(Lit(x: EntityUID)) = x.eid) (note we *only* take the id, not the type name)
    ///          phi(Record) = json format of record, with each field value interpreted by phi
    ///          phi(Set) = array, with each value interpreted by phi
    ///
    /// Similarly we can translate entity stores S into databases phi(S) as follows:
    /// each entity gets a table, with each field interpreted by phi.
    /// We ignore columns with null-values
    /// so on databases, phi is actually a multi-valued function (we say S ~ S' when the entity store S
    /// corresponds to the database S').
    ///
    /// Then we want `expr_to_sql_query` to translate an expression e to a query q
    /// such that for any assignment of unknowns (x_1, x_2, ... x_n : Value) and an entity store S and
    /// database S' such that S ~ S', we have that phi(eval(e[x_1, x_2, ... x_n], S)) = eval(q[phi(x_1), ... phi(x_n)], S')
    ///
    /// There are two kinds of unknowns: true unknowns (regular variables), and "dummy unknowns,"
    /// where dummy unknowns appear on the left side of a `GetAttr` and have "entity" as their type.
    /// We can't get the attribute of an unknown entity (since entities are represented by their string/id)
    /// without some kind of JOIN. These dummy unkowns function as follows: substituting a particular value
    /// `e` for the dummy unknown `x` should correspond to substituting S[e]'s attributes as
    /// the SQL values `x`.`attr` for each attribute `attr` of `e`.
    ///
    /// Note: we assume `e` does not depend on any variable, such as `principal`, `resource`, `context`, etc.
    ///       (if they are meant to be unknowns, they should be replaced by unknowns already)
    ///       In addition, we assume `e` typechecks
    ///
    /// `ein` should take two expressions `a` and `b` which would evaluate to string ids of the entities of the corresponding types,
    /// and return an expression determining whether `a` is in `b`
    pub fn to_sql_query(&self, ein: &impl Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>) -> Result<SimpleExpr> {
        match self {
            QueryExpr::Lit(l) => Ok(Self::lit_to_sql(l)),
            QueryExpr::Unknown { name, .. } => match name {
                UnknownType::EntityDeref(e) => Ok((Alias::new(e.clone()), Alias::new("uid")).into_column_ref().into()),
                UnknownType::Other(c) => Ok(c.clone().into_column_ref().into()),
            },
            QueryExpr::If { test_expr, then_expr, else_expr } => Ok(
                sea_query::Expr::case(test_expr.to_sql_query(ein)?,
                    then_expr.to_sql_query(ein)?)
                    .finally(else_expr.to_sql_query(ein)?).into()),
            QueryExpr::And { left, right } => Ok(left.to_sql_query(ein)?.and(right.to_sql_query(ein)?)),
            QueryExpr::Or { left, right } => Ok(left.to_sql_query(ein)?.or(right.to_sql_query(ein)?)),
            QueryExpr::UnaryApp { op, arg } => match op {
                UnaryOp::Not => Ok(arg.to_sql_query(ein)?.not()),
                UnaryOp::Neg => Ok(arg.to_sql_query(ein)?.mul(-1)), // TODO: find unary negation operator
            },
            QueryExpr::BinaryApp { op, left, right } => {
                let left = left.to_sql_query(ein)?;
                let right = right.to_sql_query(ein)?;
                match op {
                    BinaryOp::In => panic!("Internal invariant violated: binary app operator is `in`, should use `InEntity` or `InSet` instead"),
                    BinaryOp::Contains => {
                        Ok(left.eq(PgFunc::any(right)))
                    },
                    _ => Ok(left.binary(cedar_binary_to_sql_binary(*op).unwrap(), right))
                }
            },
            QueryExpr::InEntity { left, right, left_type, right_type } => {
                ein(left_type, right_type, left.to_sql_query(ein)?, right.to_sql_query(ein)?)
            },
            QueryExpr::InSet { .. } => {
                unimplemented!("TODO: implement InSet")
            },
            QueryExpr::MulByConst { arg, constant } => {
                Ok(arg.to_sql_query(ein)?.mul(*constant))
            },
            QueryExpr::GetAttrEntity { expr, attr, .. } => {
                Ok((Alias::new(expr.get_unknown_entity_deref_name().ok_or(QueryExprError::NotAttrReducedGetAttrEntity)?),
                    Alias::new(attr.as_str())).into_column_ref().into())
            },
            QueryExpr::GetAttrRecord { expr, attr, result_type } => {
                let left = expr.to_sql_query(ein)?;
                match result_type {
                    CastableType::Bool => Ok(left.get_json_field(attr.as_str()).cast_as(Alias::new("boolean"))),
                    CastableType::Long => Ok(left.get_json_field(attr.as_str()).cast_as(Alias::new("integer"))), // TODO: use bigint?
                    CastableType::StringOrEntity => Ok(left.cast_json_field(attr.as_str())),
                    CastableType::Set => unimplemented!("Retrieving sets from records unimplemented (would require json-to-array conversion, not sure how to do that"),
                    CastableType::Record => Ok(left.get_json_field(attr.as_str())),
                }
            },
            QueryExpr::HasAttrRecord { expr, attr } => {
                Ok(expr.to_sql_query(ein)?.binary(BinOper::Custom("?"), attr.as_str()))
            },
            QueryExpr::IsNotNull(expr) => Ok(expr.to_sql_query(ein)?.binary(BinOper::IsNot, Keyword::Null)),
            QueryExpr::Like { .. } => unimplemented!("TODO: implement LIKE"),
            QueryExpr::Set(_) => unimplemented!("TODO: implement Set"),
            QueryExpr::Record { .. } => unimplemented!("TODO: implement Record"),
        }
    }


    /// Wrapper around `to_sql_query` where `ein_table` should return the ordered pair (table, col1, col2)
    pub fn to_sql_query_ein_table<A, B, C>(&self, ein_table: &impl Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, C)>) -> Result<SimpleExpr>
            where A: IntoIden + Clone + 'static, B: IntoIden + Clone + 'static, C: IntoIden + Clone + 'static {
        self.to_sql_query(&|tp1, tp2, e1, e2| {
            let (tbl, col1, col2) = ein_table(tp1, tp2)?;
            let sub_query = Query::select()
                .column((tbl.clone(), col2.clone()).into_column_ref())
                .from(tbl.clone())
                .and_where(sea_query::Expr::col(col1).eq(e1))
                .to_owned();
            // e2 in (SELECT tbl.col2 FROM tbl WHERE tbl.col1 = e1)
            Ok(e2.binary(BinOper::In, SimpleExpr::SubQuery(
                None,
                Box::new(sub_query.into_sub_query_statement())
            )))
        })
    }
}

impl ExprWithBindings {
    pub fn to_sql_query<A, B, C>(&self, ein: &impl Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, C)>) -> Result<SelectStatement>
            where A: IntoIden + Clone + 'static, B: IntoIden + Clone + 'static, C: IntoIden + Clone + 'static {
        let mut query = Query::select();
        query.and_where(self.expr.to_sql_query_ein_table(ein)?);
        for (bv, e) in self.bindings.iter() {
            query.join_as(sea_query::JoinType::InnerJoin,
                Alias::new(bv.ty.basename()), Alias::new(bv.name.clone()),
                e.to_sql_query_ein_table(ein)?.eq((Alias::new(bv.name.clone()), Alias::new("uid")).into_column_ref()));
        }
        Ok(query)
    }
}

/// Does the translation from Cedar to SQL without any renaming
pub fn translate_expr<A, B, C>(expr: &Expr, schema: &Schema, ein_table: &impl Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, C)>) -> Result<SelectStatement>
        where A: IntoIden + Clone + 'static, B: IntoIden + Clone + 'static, C: IntoIden + Clone + 'static {
    let typechecker = Typechecker::new(&schema.0, ValidationMode::Strict);
    let req_env = RandomRequestEnv::new();
    let typed_expr = typechecker.typecheck_expr_strict(&(&req_env).into(), expr, cedar_policy_validator::types::Type::primitive_boolean(), &mut Vec::new())
        .ok_or(QueryExprError::TypecheckError)?;

    let query_expr: QueryExpr<SmolStr> = (&typed_expr).try_into()?;
    let query_expr_mapped: QueryExpr = query_expr.into();

    let mut query_with_bindings: ExprWithBindings = query_expr_mapped.into();
    query_with_bindings.reduce_attrs(&mut IdGen::new());


    query_with_bindings.to_sql_query(ein_table)
}


pub fn translate_response<A, B, C>(resp: &ResidualResponse, schema: &Schema, ein_table: &impl Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, C)>) -> Result<SelectStatement>
        where A: IntoIden + Clone + 'static, B: IntoIden + Clone + 'static, C: IntoIden + Clone + 'static {
    let (permits, forbids): (Vec<_>, Vec<_>) =
        resp.residuals().policies()
            .partition(|p| p.effect() == Effect::Permit);
    let expr: Expr = ExprBuilder::new().and(
        ExprBuilder::new().any(permits.into_iter().map(|p| p.non_head_constraints().clone())),
        ExprBuilder::new().not(ExprBuilder::new().any(forbids.into_iter().map(|p| p.non_head_constraints().clone()))));
    translate_expr(&expr, schema, ein_table)
}

#[cfg(test)]
mod test {
    use cedar_policy::Schema;
    use cedar_policy_core::{evaluator::RestrictedEvaluator, extensions::Extensions, ast};
    use sea_query::{Alias, PostgresQueryBuilder, Asterisk};

    use super::translate_expr;

    /// Translation function for the purposes of testing; fills in lots of boilerplate
    pub fn translate_expr_test(expr: ast::Expr, schema: &Schema) -> String {
        let ext = Extensions::all_available();
        let eval = RestrictedEvaluator::new(&ext);
        let expr = eval.partial_interpret_unrestricted(&expr, &["unknown".parse().unwrap()].into()).unwrap();

        let mut query = translate_expr(&expr, schema, &|t1, t2| {
            let t1_str = t1.to_string();
            let t2_str = t2.to_string();
            let in_table = format!("{}_in_{}", t1_str, t2_str);
            Ok((Alias::new(in_table), Alias::new(t1_str), Alias::new(t2_str)))
        }).unwrap();

        query
            .column(Asterisk)
            .from(Alias::new("resource"))
            .to_string(PostgresQueryBuilder)
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
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE "resource"."owner" = '0'"#);
    }

    #[test]
    fn test_entity_deref_id() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos") == Photos::"0""#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE "resource"."uid" = '0'"#);
    }

    #[test]
    fn test_if() {
        let result = translate_expr_test(
            r#"(if unknown("resource: Photos").owner == Users::"0" then Photos::"beach" else Photos::"carnival") == unknown("resource: Photos").nextPhoto"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE (CASE WHEN ("resource"."owner" = '0') THEN 'beach' ELSE 'carnival' END) = "resource"."nextPhoto""#);
    }

    #[test]
    fn test_nested_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown("resource: Photos").owner.level"#.parse().unwrap(),
            &get_schema(),
        );
        assert_eq!(result, r#"SELECT * FROM "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE 5 <= "v__entity_attr_0"."level""#);
    }

    #[test]
    fn test_deeply_nested_getattr() {
        let result = translate_expr_test(
            r#"unknown("resource: Photos").nextPhoto.nextPhoto.nextPhoto.owner.level == 3"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" INNER JOIN "Photos" AS "v__entity_attr_0" ON "resource"."nextPhoto" = "v__entity_attr_0"."uid" INNER JOIN "Photos" AS "v__entity_attr_1" ON "v__entity_attr_0"."nextPhoto" = "v__entity_attr_1"."uid" INNER JOIN "Photos" AS "v__entity_attr_2" ON "v__entity_attr_1"."nextPhoto" = "v__entity_attr_2"."uid" INNER JOIN "Users" AS "v__entity_attr_3" ON "v__entity_attr_2"."owner" = "v__entity_attr_3"."uid" WHERE "v__entity_attr_3"."level" = 3"#);
    }

    #[test]
    fn test_double_getattr() {
        let result = translate_expr_test(
            r#"5 <= unknown("resource: Photos").owner.level && unknown("resource: Photos").owner.level <= 10"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE (5 <= "v__entity_attr_0"."level") AND ("v__entity_attr_0"."level" <= 10)"#);
    }

    #[test]
    fn test_if_getattr() {
        let result = translate_expr_test(
            r#"(if unknown("resource: Photos") == Photos::"0" || unknown("resource: Photos") == Photos::"1" then unknown("resource: Photos") else unknown("resource: Photos").nextPhoto).owner == Users::"2""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" INNER JOIN "Photos" AS "v__entity_attr_0" ON (CASE WHEN (("resource"."uid" = '0') OR ("resource"."uid" = '1')) THEN "resource"."uid" ELSE "resource"."nextPhoto" END) = "v__entity_attr_0"."uid" WHERE "v__entity_attr_0"."owner" = '2'"#);
    }

    #[test]
    fn test_in() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos") in Users::"0""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE '0' IN (SELECT "Photos_in_Users"."Users" FROM "Photos_in_Users" WHERE "Photos" = "resource"."uid")"#);
    }

    #[test]
    fn test_in2() {
        let result: String = translate_expr_test(
            r#"Users::"0" in unknown("resource: Photos")"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE "resource"."uid" IN (SELECT "Users_in_Photos"."Photos" FROM "Users_in_Photos" WHERE "Users" = '0')"#);
    }

    #[test]
    fn test_in3() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos") in unknown("resource: Photos").nextPhoto"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE "resource"."nextPhoto" IN (SELECT "Photos_in_Photos"."Photos" FROM "Photos_in_Photos" WHERE "Photos" = "resource"."uid")"#);
    }

    #[test]
    fn test_record_attr() {
        let result: String = translate_expr_test(
            r#"unknown("resource: Photos").owner.info.name == "Bob""#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" INNER JOIN "Users" AS "v__entity_attr_0" ON "resource"."owner" = "v__entity_attr_0"."uid" WHERE "v__entity_attr_0"."info" ->> 'name' = 'Bob'"#)
    }
}
