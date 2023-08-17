use cedar_policy::{EntityTypeName, Schema, RandomRequestEnv, ResidualResponse, Effect};
use cedar_policy_core::ast::{Literal, UnaryOp, BinaryOp, Expr, ExprBuilder};
use cedar_policy_validator::{typecheck::Typechecker, ValidationMode};
use sea_query::{SimpleExpr, IntoColumnRef, BinOper, extension::postgres::{PgBinOper, PgExpr}, Alias, IntoIden, Query, Keyword, PgFunc, SelectStatement, IntoTableRef};
use thiserror::Error;

use crate::query_expr::{QueryExprError, QueryExpr, UnknownType, CastableType, ExprWithBindings, IdGen, AttrOrId};

#[derive(Debug, Error)]
pub enum ExprToSqlError {
    #[error("some error occured: {0}")]
    StringError(String),
}

type Result<T> = std::result::Result<T, QueryExprError>;

pub trait InConfig {
    fn ein(&self, tp1: &EntityTypeName, tp2: &EntityTypeName, e1: SimpleExpr, e2: SimpleExpr) -> Result<SimpleExpr>;

    fn ein_set(&self, tp1: &EntityTypeName, tp2: &EntityTypeName, e1: SimpleExpr, e2: SimpleExpr) -> Result<SimpleExpr>;
}

pub struct InByLambda<S, T>
    where S: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
          T: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
{
    pub ein: S,
    pub ein_set: T,
}

pub struct InByTable<A, B, T>(pub T)
    where A: IntoIden, B: IntoIden,
          T: Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, B)>;

impl<A, B, T> InConfig for InByTable<A, B, T>
    where A: IntoIden, B: IntoIden,
          T: Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, B)> {
    fn ein(&self, tp1: &EntityTypeName, tp2: &EntityTypeName, e1: SimpleExpr, e2: SimpleExpr) -> Result<SimpleExpr> {
        let (tbl, col1, col2) = self.0(tp1, tp2)?;
        let tbl = tbl.into_iden();
        let col1 = col1.into_iden();
        let col2 = col2.into_iden();
        let col1 = (tbl.clone(), col1).into_column_ref();
        let col2 = (tbl.clone(), col2).into_column_ref();

        // e2 in (SELECT tbl.col2 FROM tbl WHERE tbl.col1 = e1)
        let sub_query = Query::select()
            .column(col2)
            .from(tbl)
            .and_where(sea_query::Expr::col(col1).eq(e1))
            .to_owned();
        Ok(e2.binary(BinOper::In, SimpleExpr::SubQuery(
            None,
            Box::new(sub_query.into_sub_query_statement())
        )))
    }

    fn ein_set(&self, tp1: &EntityTypeName, tp2: &EntityTypeName, e1: SimpleExpr, e2: SimpleExpr) -> Result<SimpleExpr> {
        let (tbl, col1, col2) = self.0(tp1, tp2)?;
        let tbl = tbl.into_iden();
        let col1 = col1.into_iden();
        let col2 = col2.into_iden();
        let col1 = (tbl.clone(), col1).into_column_ref();
        let col2 = (tbl.clone(), col2).into_column_ref();

        // e1 in (SELECT tbl.col1 FROM tbl WHERE tbl.col2 = ANY(e2))
        let sub_query = Query::select()
            .column(col1)
            .from(tbl)
            .and_where(sea_query::Expr::col(col2).eq(PgFunc::any(e2)))
            .to_owned();
        Ok(e1.binary(BinOper::In, SimpleExpr::SubQuery(
            None,
            Box::new(sub_query.into_sub_query_statement())
        )))
    }


}


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

impl IntoColumnRef for UnknownType {
    fn into_column_ref(self) -> sea_query::ColumnRef {
        match self.pfx {
            Some(pfx) => (Alias::new(pfx), Alias::new(self.name)).into_column_ref(),
            None => Alias::new(self.name).into_column_ref(),
        }
    }
}

impl IntoIden for AttrOrId {
    fn into_iden(self) -> sea_query::DynIden {
        match self {
            AttrOrId::Attr(s) => Alias::new(s.as_str()).into_iden(),
            AttrOrId::Id(s) => Alias::new(s.as_str()).into_iden(),
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
    pub fn to_sql_query(&self, ein: &impl InConfig) -> Result<SimpleExpr> {
        match self {
            QueryExpr::Lit(l) => Ok(Self::lit_to_sql(l)),
            QueryExpr::Unknown { name, type_annotation } => {
                if type_annotation.is_none() {
                    Ok(name.clone().into_column_ref().into())
                } else { Err(QueryExprError::NotAttrReduced(name.name.clone())) }
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
                        Ok(right.eq(PgFunc::any(left)))
                    },
                    _ => Ok(left.binary(cedar_binary_to_sql_binary(*op).unwrap(), right))
                }
            },
            QueryExpr::InEntity { left, right, left_type, right_type } => {
                ein.ein(left_type, right_type, left.to_sql_query(ein)?, right.to_sql_query(ein)?)
            },
            QueryExpr::InSet { left, right, left_type, right_type } => {
                ein.ein_set(left_type, right_type, left.to_sql_query(ein)?, right.to_sql_query(ein)?)
            },
            QueryExpr::MulByConst { arg, constant } => {
                Ok(arg.to_sql_query(ein)?.mul(*constant))
            },
            QueryExpr::GetAttrEntity { expr, attr, .. } => {
                Ok((Alias::new(expr.get_unknown_entity_deref_name().ok_or(QueryExprError::NotAttrReducedGetAttrEntity)?),
                    attr.clone()).into_column_ref().into())
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
}

impl ExprWithBindings {
    pub fn to_sql_query<T: IntoTableRef, U: IntoIden>(&self, ein: &impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<SelectStatement> {
        let mut query = Query::select();
        query.and_where(self.expr.to_sql_query(ein)?);
        for (bv, e) in self.bindings.iter() {
            let (tbl_ref, id_name) = table_names(&bv.ty);
            let id_name = id_name.into_iden();
            query.join_as(sea_query::JoinType::InnerJoin,
                tbl_ref, Alias::new(bv.name.clone()),
                e.to_sql_query(ein)?.eq((Alias::new(bv.name.clone()), id_name).into_column_ref()));
        }
        Ok(query)
    }
}

/// Does the translation from Cedar to SQL
pub fn translate_expr<T: IntoTableRef, U: IntoIden>(expr: &Expr, schema: &Schema, ein: &impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<SelectStatement> {
    let typechecker = Typechecker::new(&schema.0, ValidationMode::Strict);
    let req_env = RandomRequestEnv::new();
    let typed_expr = typechecker.typecheck_expr_strict(&(&req_env).into(), expr, cedar_policy_validator::types::Type::primitive_boolean(), &mut Vec::new())
        .ok_or(QueryExprError::TypecheckError)?;

    let query_expr: QueryExpr = (&typed_expr).try_into()?;

    let mut query_with_bindings: ExprWithBindings = query_expr.into();
    query_with_bindings.reduce_attrs(&mut IdGen::new());

    query_with_bindings.to_sql_query(ein, table_names)
}


pub fn translate_response<T: IntoTableRef, U: IntoIden>(resp: &ResidualResponse, schema: &Schema, ein: &impl InConfig, table_names: impl Fn(&EntityTypeName) -> (T, U)) -> Result<SelectStatement> {
    let (permits, forbids): (Vec<_>, Vec<_>) =
        resp.residuals().policies()
            .partition(|p| p.effect() == Effect::Permit);
    let expr: Expr = ExprBuilder::new().and(
        ExprBuilder::new().any(permits.into_iter().map(|p| p.non_head_constraints().clone())),
        ExprBuilder::new().not(ExprBuilder::new().any(forbids.into_iter().map(|p| p.non_head_constraints().clone()))));
    translate_expr(&expr, schema, ein, table_names)
}

#[cfg(test)]
mod test {
    use cedar_policy::Schema;
    use cedar_policy_core::{evaluator::RestrictedEvaluator, extensions::Extensions, ast};
    use sea_query::{Alias, PostgresQueryBuilder, Asterisk};

    use super::{translate_expr, InByTable};

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
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE '0' IN (SELECT "Photos_in_Users"."Users" FROM "Photos_in_Users" WHERE "Photos_in_Users"."Photos" = "resource"."uid")"#);
    }

    #[test]
    fn test_in2() {
        let result: String = translate_expr_test(
            r#"Users::"0" in unknown("resource: Photos")"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE "resource"."uid" IN (SELECT "Users_in_Photos"."Photos" FROM "Users_in_Photos" WHERE "Users_in_Photos"."Users" = '0')"#);
    }

    #[test]
    fn test_inset() {
        let result: String = translate_expr_test(
            r#"Photos::"0" in unknown("resource: Users").allowedPhotos"#.parse().unwrap(),
            &get_schema()
        );
        assert_eq!(result, r#"SELECT * FROM "resource" WHERE ('0' = ANY("resource"."allowedPhotos")) OR ('0' IN (SELECT "Photos_in_Photos"."Photos" FROM "Photos_in_Photos" WHERE "Photos_in_Photos"."Photos" = ANY("resource"."allowedPhotos")))"#)
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
