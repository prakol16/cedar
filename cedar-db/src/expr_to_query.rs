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

//! This module contains methods to convert the QueryExpr IR to
//! sea query abstract syntax trees for SQL queries.
use cedar_policy::EntityTypeName;
use cedar_policy_core::ast::{BinaryOp, Literal, Pattern, PatternElem, UnaryOp};
use sea_query::{
    extension::postgres::{PgBinOper, PgExpr},
    Alias, BinOper, Func, Iden, IntoColumnRef, IntoIden, Keyword, LikeExpr, PgFunc,
    PostgresQueryBuilder, Query, SimpleExpr, TableRef,
};
use smol_str::SmolStr;

use crate::{
    query_expr::{AttrOrId, QueryExpr, QueryExprError, QueryPrimitiveType, QueryType, UnknownType},
    sea_query_extra::StaticTableRef,
};

type Result<T> = std::result::Result<T, QueryExprError>;

/// A trait for configuring the `ein` and `ein_set` functions
/// See `InByTable` for a reasonable default implementation that implements these by assuming
/// there is a table that stores all ancestry information.
pub trait InConfig {
    /// `ein` determines how to translate the Cedar `in` statement. It takes in two entity types,
    /// and two sea query expressions e1 and e2, where e1 and e2, when evaluated, will produce the ids
    /// of the corresponding entities. It should return an expression determining whether e1 is a descendant of e2.
    fn ein(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr>;

    /// `ein_set` determines how to translate the Cedar `in` statement when the right hand side is a set.
    /// It works the same way as `ein`, except the expression `e2` will evaluate to a postgres array.
    fn ein_set(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr>;
}

impl<T: InConfig> InConfig for &T {
    fn ein(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        (*self).ein(tp1, tp2, e1, e2)
    }

    fn ein_set(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        (*self).ein_set(tp1, tp2, e1, e2)
    }
}

/// Construct an `InConfig` from two lambda functions `ein` and `ein_set`
#[derive(Debug, Clone)]
pub struct InByLambda<S, T>
where
    S: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
    T: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
{
    /// `ein` corresponds to InConfig::ein
    pub ein: S,
    /// `ein_set` corresponds to InConfig::ein_set
    pub ein_set: T,
}

impl<S, T> InConfig for InByLambda<S, T>
where
    S: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
    T: Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>,
{
    fn ein(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        (self.ein)(tp1, tp2, e1, e2)
    }

    fn ein_set(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        (self.ein_set)(tp1, tp2, e1, e2)
    }
}

/// Construct an `InConfig` from a function that takes in two entity types and returns an optional
/// tuple of (table, column1, column2) where table is the table that stores ancestry information,
/// column1 is the column that stores the descendant, and column2 is the column that stores the ancestor.
/// If the result is None, then the translation of the expression is "false" (e.g. because it is impossible
/// for one entity to be a descendant of the other)
#[derive(Debug, Clone)]
pub struct InByTable<A, B, T>(pub T)
where
    A: Into<StaticTableRef>,
    B: IntoIden,
    T: Fn(&EntityTypeName, &EntityTypeName) -> Result<Option<(A, B, B)>>;

impl<A, B, T> InConfig for InByTable<A, B, T>
where
    A: Into<StaticTableRef>,
    B: IntoIden,
    T: Fn(&EntityTypeName, &EntityTypeName) -> Result<Option<(A, B, B)>>,
{
    fn ein(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        if let Some((tbl, col1, col2)) = self.0(tp1, tp2)? {
            let tbl: StaticTableRef = tbl.into();
            let col1 = tbl.clone().with_column(col1);
            let col2 = tbl.clone().with_column(col2);

            // e2 in (SELECT tbl.col2 FROM tbl WHERE tbl.col1 = e1)
            let sub_query = Query::select()
                .column(col2)
                .from(tbl)
                .and_where(sea_query::Expr::col(col1).eq(e1))
                .to_owned();
            Ok(e2.binary(
                BinOper::In,
                SimpleExpr::SubQuery(None, Box::new(sub_query.into_sub_query_statement())),
            ))
        } else {
            Ok(false.into())
        }
    }

    fn ein_set(
        &self,
        tp1: &EntityTypeName,
        tp2: &EntityTypeName,
        e1: SimpleExpr,
        e2: SimpleExpr,
    ) -> Result<SimpleExpr> {
        if let Some((tbl, col1, col2)) = self.0(tp1, tp2)? {
            let tbl: StaticTableRef = tbl.into();
            let col1 = tbl.clone().with_column(col1);
            let col2 = tbl.clone().with_column(col2);

            // e1 in (SELECT tbl.col1 FROM tbl WHERE tbl.col2 = ANY(e2))
            let sub_query = Query::select()
                .column(col1)
                .from(tbl)
                .and_where(sea_query::Expr::col(col2).eq(PgFunc::any(e2)))
                .to_owned();
            Ok(e1.binary(
                BinOper::In,
                SimpleExpr::SubQuery(None, Box::new(sub_query.into_sub_query_statement())),
            ))
        } else {
            Ok(false.into())
        }
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
        let name = self.get_name();
        if let Some(pfx) = self.get_pfx() {
            (Alias::new(pfx), Alias::new(name)).into_column_ref()
        } else {
            Alias::new(name).into_column_ref()
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

impl IntoIden for QueryPrimitiveType {
    fn into_iden(self) -> sea_query::DynIden {
        match self {
            QueryPrimitiveType::Bool => Alias::new("boolean").into_iden(),
            QueryPrimitiveType::Long => Alias::new("bigint").into_iden(),
            QueryPrimitiveType::StringOrEntity => Alias::new("text").into_iden(),
            QueryPrimitiveType::Record => Alias::new("jsonb").into_iden(),
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
            }
        }
    }

    fn mk_postgres_array(elems: Vec<SimpleExpr>) -> SimpleExpr {
        let mut result: String = "ARRAY[".into();
        result.push_str(
            elems
                .into_iter()
                .map(|elem| {
                    // Words cannot express how ugly of a hack this is
                    // Waiting on something like https://github.com/SeaQL/sea-query/issues/683
                    // to fix this
                    sea_query::Query::select()
                        .expr(elem)
                        .to_string(PostgresQueryBuilder)
                        .replacen("SELECT ", "", 1)
                })
                .collect::<Vec<_>>()
                .join(", ")
                .as_str(),
        );
        result.push(']');
        sea_query::Expr::cust(result)
    }

    fn mk_postgres_record(elems: Vec<(SmolStr, SimpleExpr)>) -> SimpleExpr {
        #[derive(Iden)]
        #[iden = "jsonb_build_object"]
        struct BuildObjectFunc;

        let mut args: Vec<SimpleExpr> = Vec::with_capacity(elems.len() * 2);
        for (k, v) in elems {
            args.push(k.as_str().into());
            args.push(v);
        }

        Func::cust(BuildObjectFunc).args(args).into()
    }

    fn pattern_to_likeexpr(p: &Pattern) -> LikeExpr {
        fn escape_char(s: &mut String, c: char) {
            if c == '%' || c == '_' || c == '\\' {
                s.push('\\');
            }
        }

        let mut result: String = String::new();
        for c in p.iter() {
            match c {
                PatternElem::Char(c) => {
                    escape_char(&mut result, *c);
                    result.push(*c);
                }
                PatternElem::Wildcard => {
                    result.push('%');
                }
            }
        }
        LikeExpr::new(result).escape('\\')
    }

    /// Given an expression `e` that returns a JSON nested array of type `tp`,
    /// cast the result to a postgres nested array
    fn cast_json(e: SimpleExpr, tp: QueryType) -> SimpleExpr {
        // Aggregate the set into an array
        #[derive(Iden)]
        #[iden = "Array"]
        struct ArrayFunc;

        // Get the array elements as a set
        #[derive(Iden)]
        #[iden = "jsonb_array_elements"]
        struct ArrayElemsFunc;

        // Get the array elements and cast to text
        #[derive(Iden)]
        #[iden = "jsonb_array_elements_text"]
        struct ArrayElemsTextFunc;

        match tp {
            // If the result type is a record, we don't need to do any casting
            QueryType::Primitive(QueryPrimitiveType::Record) => e,
            // At 0 depth, we just cast the array
            QueryType::Primitive(tp) => e.cast_as(tp),
            QueryType::Array(tp) => {
                let alias_name: Alias = Alias::new("result");
                let col_ref = (alias_name.clone(), Alias::new("value")).into_column_ref();

                Func::cust(ArrayFunc)
                    .arg(SimpleExpr::SubQuery(
                        None,
                        Box::new({
                            // There is a special function for casting json text array to postgres text array
                            if tp == QueryPrimitiveType::StringOrEntity {
                                let mut subquery = Query::select();
                                subquery.expr(sea_query::Expr::col(col_ref));
                                subquery.from(TableRef::FunctionCall(
                                    Func::cust(ArrayElemsTextFunc).arg(e),
                                    alias_name.into_iden(),
                                ));
                                subquery.into_sub_query_statement()
                            } else {
                                let mut subquery = Query::select();
                                subquery.expr(Self::cast_json(
                                    col_ref.into(),
                                    QueryType::Primitive(tp),
                                ));
                                subquery.from(TableRef::FunctionCall(
                                    Func::cust(ArrayElemsFunc).arg(e),
                                    alias_name.into_iden(),
                                ));
                                subquery.into_sub_query_statement()
                            }
                        }),
                    ))
                    .into()
            }
        }
    }

    /// Semantics:
    /// Let r: Value -> SQLValue -> {0, 1} be a relation  which interprets Cedar values as SQL values.
    /// We say (e: Value) corresponds to (e' SQLValue) (i.e. e ~ e') if r(e, e').
    /// Note that multiple different Cedar values can correspond to the same SQL value, since
    /// entity uids are converted to strings corresponding to their ids.
    /// Similarly, a single Cedar value can correspond to multiple SQL values, since a Cedar
    /// set can correspond to a SQL array in any order.
    ///
    /// Note that we assume array and json extensions to SQL, both of which are present in
    /// some dialects e.g. PostgresQL, but missing in e.g. SQLite.
    ///
    /// Similarly we can associate entity stores S with SQL databases S' (S ~ S') as follows:
    /// each entity gets a table, with each field interpreted by r. Missing optional attributes
    /// become nulls.
    ///
    /// Then we want `expr_to_sql_query` to translate an expression e to a query q
    /// such that for any assignment of unknowns (x_1, x_2, ... x_n : Value) with corresponding sql values
    /// (x_1' ~ x_1, x_2' ~ x_2, ... x_n' ~ x_n), and any entity store S with database S' such that S ~ S',
    ///  we have that eval(e[x_1, x_2, ... x_n], S) ~ eval(q[x_1', x_2', ... x_n'], S')
    ///
    /// Note: we assume `e` does not depend on any variable, such as `principal`, `resource`, `context`, etc.
    ///       (if they are meant to be unknowns, they should be replaced by unknowns already)
    ///       In addition, we assume `e` strict typechecks. Finally, we assume `e` is attribute reduced.
    ///
    /// `ein` should take two expressions `a` and `b` which would evaluate to string ids of the entities of the corresponding types,
    /// and return an expression determining whether `a` is in `b` satisfying the above spec
    pub fn to_sql_query(&self, ein: &impl InConfig) -> Result<SimpleExpr> {
        match self {
            QueryExpr::Lit(l) => Ok(Self::lit_to_sql(l)),
            QueryExpr::Unknown(UnknownType::NonEntityType { pfx, name }) => {
                if let Some(pfx) = pfx {
                    Ok((Alias::new(pfx.as_str()), Alias::new(name.as_str()))
                        .into_column_ref()
                        .into())
                } else {
                    Ok(Alias::new(name.as_str()).into_column_ref().into())
                }
            }
            QueryExpr::Unknown(UnknownType::EntityType { name, .. }) => {
                Err(QueryExprError::NotAttrReduced(name.clone()))
            }
            QueryExpr::If {
                test_expr,
                then_expr,
                else_expr,
            } => Ok(sea_query::Expr::case(
                test_expr.to_sql_query(ein)?,
                then_expr.to_sql_query(ein)?,
            )
            .finally(else_expr.to_sql_query(ein)?)
            .into()),
            QueryExpr::And { left, right } => {
                Ok(left.to_sql_query(ein)?.and(right.to_sql_query(ein)?))
            }
            QueryExpr::Or { left, right } => {
                Ok(left.to_sql_query(ein)?.or(right.to_sql_query(ein)?))
            }
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
                    _ => {
                        // PANIC SAFETY We manually checked for `In` and `Contains` above
                        #[allow(clippy::unwrap_used)]
                        Ok(left.binary(cedar_binary_to_sql_binary(*op).unwrap(), right))
                    }
                }
            }
            QueryExpr::InEntity {
                left,
                right,
                left_type,
                right_type,
            } => ein.ein(
                left_type,
                right_type,
                left.to_sql_query(ein)?,
                right.to_sql_query(ein)?,
            ),
            QueryExpr::InSet {
                left,
                right,
                left_type,
                right_type,
            } => ein.ein_set(
                left_type,
                right_type,
                left.to_sql_query(ein)?,
                right.to_sql_query(ein)?,
            ),
            QueryExpr::MulByConst { arg, constant } => Ok(arg.to_sql_query(ein)?.mul(*constant)),
            QueryExpr::GetAttrEntity { expr, attr, .. } => Ok((
                Alias::new(
                    expr.get_unknown_entity_deref_name()
                        .ok_or(QueryExprError::NotAttrReducedGetAttrEntity)?,
                ),
                attr.clone(),
            )
                .into_column_ref()
                .into()),
            QueryExpr::GetAttrRecord {
                expr,
                attr,
                result_type,
            } => {
                let left = expr.to_sql_query(ein)?;
                match result_type {
                    // If the result type is a string, there is a special function in postgres to handle this case
                    QueryType::Primitive(QueryPrimitiveType::StringOrEntity) => {
                        Ok(left.cast_json_field(attr.as_str()))
                    }
                    // `cast_array` correctly handles the base case of 0 nesting (non-array) values as well
                    _ => Ok(Self::cast_json(
                        left.get_json_field(attr.as_str()),
                        *result_type,
                    )),
                }
            }
            QueryExpr::HasAttrRecord { expr, attr } => Ok(expr
                .to_sql_query(ein)?
                .binary(BinOper::Custom("?"), attr.as_str())),
            QueryExpr::IsNotNull(expr) => Ok(expr
                .to_sql_query(ein)?
                .binary(BinOper::IsNot, Keyword::Null)),
            QueryExpr::Like { expr, pattern } => Ok(expr
                .to_sql_query(ein)?
                .like(Self::pattern_to_likeexpr(pattern))),
            QueryExpr::Set(values) => Ok(Self::mk_postgres_array(
                values
                    .iter()
                    .map(|v| v.to_sql_query(ein))
                    .collect::<Result<Vec<_>>>()?,
            )),
            QueryExpr::Record { pairs } => Ok(Self::mk_postgres_record(
                pairs
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), v.to_sql_query(ein)?)))
                    .collect::<Result<Vec<_>>>()?,
            )),
            QueryExpr::RawSQL { sql, args } => {
                let args = args
                    .iter()
                    .map(|v| v.to_sql_query(ein))
                    .collect::<Result<Vec<_>>>()?;
                Ok(sea_query::Expr::cust_with_exprs(sql.to_string(), args))
            }
        }
    }
}
