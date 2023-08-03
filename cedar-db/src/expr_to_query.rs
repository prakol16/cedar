use std::fmt;

use cedar_policy_core::ast::{Expr, ExprKind, Literal, Eid};
use sea_query::{Query, SimpleExpr, Iden, Condition, IntoColumnRef};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExprToSqlError {
    #[error("some error occured: {0}")]
    StringError(String),
}

pub type Result<T> = std::result::Result<T, ExprToSqlError>;

pub struct EntityQueryExpr {

}


/// Alias for sea_query::Expr::expr which is too long and too frequently used
fn sqlexpr<T: Into<SimpleExpr>>(e: T) -> sea_query::Expr {
    sea_query::Expr::expr(e)
}

struct RawColumn(String);

impl Iden for RawColumn {
    fn unquoted(&self,s: &mut dyn fmt::Write) {
        write!(s, "{}", self.0).unwrap();
    }
}

fn col(s: &str) -> SimpleExpr {
    RawColumn::from(s).into_column_ref().into()
}

impl<T: Into<String>> From<T> for RawColumn {
    fn from(s: T) -> Self {
        RawColumn(s.into())
    }
}

pub fn expr_to_sql_query(e: &Expr) -> Result<SimpleExpr> {
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
        ExprKind::Unknown { name, type_annotation } => Ok(col(name.as_str())),
        ExprKind::If { test_expr, then_expr, else_expr } => todo!(),
        ExprKind::And { left, right } => Ok(expr_to_sql_query(&left)?.and(expr_to_sql_query(&right)?)),
        ExprKind::Or { left, right } => Ok(expr_to_sql_query(&left)?.or(expr_to_sql_query(&right)?)),
        ExprKind::UnaryApp { op, arg } => todo!(),
        ExprKind::BinaryApp { op, arg1, arg2 } => todo!(),
        ExprKind::MulByConst { arg, constant } => todo!(),
        ExprKind::ExtensionFunctionApp { fn_name, args } => todo!(),
        ExprKind::GetAttr { expr, attr } => todo!(),
        ExprKind::HasAttr { expr, attr } => todo!(),
        ExprKind::Like { expr, pattern } => todo!(),
        ExprKind::Set(_) => todo!(),
        ExprKind::Record { pairs } => todo!(),
    }
}
