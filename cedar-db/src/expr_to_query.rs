use cedar_policy_core::ast::{Expr, ExprKind, Literal, Eid};
use sea_query::{Query, SimpleExpr};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExprToSqlError {
    #[error("some error")]
    SomeError
}

pub type Result<T> = std::result::Result<T, ExprToSqlError>;

/// Alias for sea_query::Expr::expr which is too long and too frequently used
fn sqlexpr(e: impl Into<SimpleExpr>) -> sea_query::Expr {
    sea_query::Expr::expr(e)
}

pub fn expr_to_sql_query(e: &Expr) -> Result<sea_query::SimpleExpr> {
    match e.expr_kind() {
        ExprKind::Lit(e) => {
            match e {
                Literal::Bool(b) => Ok(b.clone().into()),
                Literal::Long(l) => Ok(l.clone().into()),
                Literal::String(s) => Ok(s.as_ref().into()),
                Literal::EntityUID(e) => Ok(<Eid as AsRef<str>>::as_ref(e.eid()).into()),
            }
        },
        ExprKind::Var(_) => Err(ExprToSqlError::SomeError),
        ExprKind::Slot(_) => Err(ExprToSqlError::SomeError),
        ExprKind::Unknown { name, type_annotation } => todo!(),
        ExprKind::If { test_expr, then_expr, else_expr } => todo!(),
        ExprKind::And { left, right } => todo!(),
        ExprKind::Or { left, right } => todo!(),
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
