use cedar_policy::EntityTypeName;
use cedar_policy_core::ast::{Expr, ExprKind, Literal, UnaryOp, BinaryOp};
use cedar_policy_validator::types::{Type, EntityRecordKind, Primitive};
use ref_cast::RefCast;
use sea_query::{SimpleExpr, IntoColumnRef, BinOper, extension::postgres::{PgBinOper, PgExpr}, Alias, IntoIden, Query};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExprToSqlError {
    #[error("some error occured: {0}")]
    StringError(String),
}

type Result<T> = std::result::Result<T, ExprToSqlError>;

pub struct EntityQueryExpr {

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
pub fn expr_to_sql_query(e: &Expr<Option<Type>>, ein: &impl Fn(&EntityTypeName, &EntityTypeName, SimpleExpr, SimpleExpr) -> Result<SimpleExpr>) -> Result<SimpleExpr> {
    match e.expr_kind() {
        ExprKind::Lit(e) => {
            match e {
                Literal::Bool(b) => Ok((*b).into()),
                Literal::Long(l) => Ok((*l).into()),
                Literal::String(s) => Ok(s.as_str().into()),
                Literal::EntityUID(e) => Ok(<SimpleExpr as From<&str>>::from(e.eid().as_ref())),
            }
        },
        ExprKind::Var(_) => Err(ExprToSqlError::StringError("variables should not appear in queries".into())),
        ExprKind::Slot(_) => Err(ExprToSqlError::StringError("slots should not appear in queries".into())),
        // todo: unknowns can contain table information
        ExprKind::Unknown { name, .. } => Ok(Alias::new(name.as_str()).into_column_ref().into()),
        ExprKind::If { test_expr, then_expr, else_expr } =>
            Ok(sea_query::Expr::case(expr_to_sql_query(test_expr, ein)?, expr_to_sql_query(then_expr, ein)?)
                .finally(expr_to_sql_query(else_expr, ein)?).into()),
        ExprKind::And { left, right } => Ok(expr_to_sql_query(&left, ein)?.and(expr_to_sql_query(&right, ein)?)),
        ExprKind::Or { left, right } => Ok(expr_to_sql_query(&left, ein)?.or(expr_to_sql_query(&right, ein)?)),
        ExprKind::UnaryApp { op, arg } => match op {
            UnaryOp::Not => Ok(expr_to_sql_query(arg, ein)?.not()),
            UnaryOp::Neg => Ok(expr_to_sql_query(arg, ein)?.mul(-1)), // todo: find unary negation operator
        },
        ExprKind::BinaryApp { op, arg1, arg2 } =>  match op {
            BinaryOp::In => {
                match arg2.data() {
                    Some(Type::Set { .. }) => unimplemented!("in set not supported yet in {e:?}"),
                    Some(Type::EntityOrRecord(EntityRecordKind::Entity(tp2))) => {
                        match arg1.data() {
                            Some(Type::EntityOrRecord(EntityRecordKind::Entity(tp1))) => {
                                if let Some(tp1) = tp1.get_single_entity() {
                                    if let Some(tp2) = tp2.get_single_entity() {
                                        ein(EntityTypeName::ref_cast(tp1), EntityTypeName::ref_cast(tp2),
                                            expr_to_sql_query(arg1, ein)?, expr_to_sql_query(arg2, ein)?)
                                    } else {
                                        Err(ExprToSqlError::StringError(format!("expression {arg2:?} could refer to many entities")))
                                    }
                                } else {
                                    Err(ExprToSqlError::StringError(format!("expression {arg1:?} could refer to many entities")))
                                }
                            },
                            _ => Err(ExprToSqlError::StringError(format!("expression {arg1:?} could refer to any entity/action entity"))),
                        }
                    },
                    Some(_) => Err(ExprToSqlError::StringError(format!("expression {arg1:?} could refer to any entity"))),
                    None => Err(ExprToSqlError::StringError(format!("In operator requires a type: {e:?}"))),
                }
            },
            BinaryOp::Contains => unimplemented!("contains not supported yet"),
            op => Ok(expr_to_sql_query(arg1, ein)?.binary(cedar_binary_to_sql_binary(*op).unwrap(), expr_to_sql_query(arg2, ein)?)),
        },
        ExprKind::MulByConst { arg, constant } => Ok(expr_to_sql_query(arg, ein)?.mul(*constant)),
        ExprKind::ExtensionFunctionApp { .. } => Err(ExprToSqlError::StringError("Extension functions not supported yet".into())),
        ExprKind::GetAttr { expr, attr } => match expr.data() {
            Some(Type::EntityOrRecord(EntityRecordKind::Record { .. })) => {
                // Depending on if the resulting expression is meant to be a literal or another record, we may or may not have to cast
                match e.data() {
                    Some(t) => match t {
                        Type::EntityOrRecord(t) => if matches!(t, EntityRecordKind::Record { .. }) {
                            Ok(expr_to_sql_query(expr, ein)?.get_json_field(attr.as_str()))
                        } else {
                            // `expr` is an entity type, so we should cast it to a string
                            Ok(expr_to_sql_query(expr, ein)?.cast_json_field(attr.as_str()))
                        },
                        // If it is a boolean or int, we should use -> and cast the json boolean value to a boolean/int
                        Type::False | Type::True | Type::Primitive { primitive_type: Primitive::Bool } =>
                            Ok(expr_to_sql_query(expr, ein)?.get_json_field(attr.as_str()).cast_as(Alias::new("boolean"))),
                        Type::Primitive { primitive_type: Primitive::Long } =>
                            Ok(expr_to_sql_query(expr, ein)?.get_json_field(attr.as_str()).cast_as(Alias::new("integer"))), // TODO: use bigint?
                        Type::Primitive { primitive_type: Primitive::String } =>
                            Ok(expr_to_sql_query(expr, ein)?.cast_json_field(attr.as_str())),
                        t => Err(ExprToSqlError::StringError(format!("type error: cannot get attribute {attr} of expression {expr:?} of type {t}")))
                    },
                    None => Err(ExprToSqlError::StringError(format!("cannot get attribute {attr} of expression {expr:?} unknown type"))),
                }
            },
            // this is how a subquery-based attribute selection mechanism might work
            // Some(Type::EntityOrRecord(EntityRecordKind::Entity(t))) => {
            //     if let Some(name) = t.get_single_entity() {
            //         let sub_query = Query::select()
            //             .column(Alias::new(name.basename().as_ref()))
            //             .from(Alias::new(name.namespace()))
            //             .and_where(sea_query::Expr::col(Alias::new("uid")).eq(expr_to_sql_query(expr)?))
            //             .to_owned();
            //         Ok(SimpleExpr::SubQuery(None, Box::new(sub_query.into_sub_query_statement())))
            //     } else {
            //         Err(ExprToSqlError::StringError(format!("expression {expr:?} could refer to more than one entity type; cannot get attribute")))
            //     }
            // },
            Some(_) => {
                match expr.expr_kind() {
                    ExprKind::Unknown { name, .. } => {
                        Ok((Alias::new(name.as_str()), Alias::new(attr.as_str())).into_column_ref().into())
                    },
                    _ => Err(ExprToSqlError::StringError(format!("GetAttribute can only be called on records or unknown (getting attribute {attr} of {expr:?}")))
                }
            },
            None => Err(ExprToSqlError::StringError(format!("cannot get attribute {attr} of expression {expr:?} unknown type"))),
        },
        ExprKind::HasAttr { .. } => unimplemented!("HasAttr unimplemented"),
        ExprKind::Like { .. } => unimplemented!("Like unimplemented"),
        ExprKind::Set(_) => unimplemented!("Set unimplemented"),
        ExprKind::Record { .. } => unimplemented!("Record unimplemented"),
    }
}

pub fn expr_to_sql_query_entity_in_table<A, B, C>(e: &Expr<Option<Type>>, entity_in_table: &impl Fn(&EntityTypeName, &EntityTypeName) -> Result<(A, B, C)>) -> Result<SimpleExpr>
    where A: IntoIden + Clone + 'static, B: IntoIden + Clone + 'static, C: IntoIden + Clone + 'static {
    expr_to_sql_query(e, &|tp1, tp2, e1, e2| {
        let (tbl, col1, col2) = entity_in_table(tp1, tp2)?;
        let sub_query = Query::select()
            .columns([(tbl.clone(), col1.clone()).into_column_ref(), (tbl.clone(), col2.clone()).into_column_ref()])
            .from(tbl)
            .and_where(sea_query::Expr::col(col1).eq(e1))
            .and_where(sea_query::Expr::col(col2).eq(e2))
            .to_owned();
        Ok(SimpleExpr::SubQuery(
            Some(sea_query::SubQueryOper::Exists),
            Box::new(sub_query.into_sub_query_statement())
        ))
    })
}

