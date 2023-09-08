use cedar_policy_core::ast::{BinaryOp, UnaryOp};

use crate::query_expr::QueryExpr;

#[derive(Debug, Clone)]
pub struct QueryExprIterator<'a> {
    /// Stack of expressions for query expression traversal
    expression_stack: Vec<(&'a QueryExpr, Option<QueryExprParentType>)>,
}

impl<'a> QueryExprIterator<'a> {
    /// Construct an expr iterator
    pub fn new(expr: &'a QueryExpr) -> Self {
        Self {
            expression_stack: vec![(expr, None)],
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum QueryExprParentType {
    If,
    And,
    Or,
    UnaryApp(UnaryOp),
    BinaryApp(BinaryOp),
    MulByConst,
    InEntity,
    InSet,
    GetAttrEntity,
    GetAttrRecord,
    HasAttrRecord,
    IsNotNull,
    Like,
    Set,
    Record,
    RawSQL,
}

impl<'a> Iterator for QueryExprIterator<'a> {
    type Item = (&'a QueryExpr, Option<QueryExprParentType>);

    fn next(&mut self) -> Option<Self::Item> {
        let (next_expr, parent) = self.expression_stack.pop()?;
        match next_expr {
            QueryExpr::Lit(_) => (),
            QueryExpr::Unknown { .. } => (),
            QueryExpr::If {
                test_expr,
                then_expr,
                else_expr,
            } => {
                self.expression_stack
                    .push((test_expr, Some(QueryExprParentType::If)));
                self.expression_stack
                    .push((then_expr, Some(QueryExprParentType::If)));
                self.expression_stack
                    .push((else_expr, Some(QueryExprParentType::If)));
            }
            QueryExpr::And { left, right } => {
                self.expression_stack
                    .push((left, Some(QueryExprParentType::And)));
                self.expression_stack
                    .push((right, Some(QueryExprParentType::And)));
            }
            QueryExpr::Or { left, right } => {
                self.expression_stack
                    .push((left, Some(QueryExprParentType::Or)));
                self.expression_stack
                    .push((right, Some(QueryExprParentType::Or)));
            }
            QueryExpr::UnaryApp { op, arg } => {
                self.expression_stack
                    .push((arg, Some(QueryExprParentType::UnaryApp(*op))));
            }
            QueryExpr::BinaryApp { op, left, right } => {
                self.expression_stack
                    .push((left, Some(QueryExprParentType::BinaryApp(*op))));
                self.expression_stack
                    .push((right, Some(QueryExprParentType::BinaryApp(*op))));
            }
            QueryExpr::InEntity { left, right, .. } => {
                self.expression_stack
                    .push((left, Some(QueryExprParentType::InEntity)));
                self.expression_stack
                    .push((right, Some(QueryExprParentType::InEntity)));
            }
            QueryExpr::InSet { left, right, .. } => {
                self.expression_stack
                    .push((left, Some(QueryExprParentType::InSet)));
                self.expression_stack
                    .push((right, Some(QueryExprParentType::InSet)));
            }
            QueryExpr::MulByConst { arg, .. } => {
                self.expression_stack
                    .push((arg, Some(QueryExprParentType::MulByConst)));
            }
            QueryExpr::GetAttrEntity { expr, .. } => {
                self.expression_stack
                    .push((expr, Some(QueryExprParentType::GetAttrEntity)));
            }
            QueryExpr::GetAttrRecord { expr, .. } => {
                self.expression_stack
                    .push((expr, Some(QueryExprParentType::GetAttrRecord)));
            }
            QueryExpr::HasAttrRecord { expr, .. } => {
                self.expression_stack
                    .push((expr, Some(QueryExprParentType::HasAttrRecord)));
            }
            QueryExpr::IsNotNull(arg) => {
                self.expression_stack
                    .push((arg, Some(QueryExprParentType::IsNotNull)));
            }
            QueryExpr::Like { expr, .. } => {
                self.expression_stack
                    .push((expr, Some(QueryExprParentType::Like)));
            }
            QueryExpr::Set(values) => {
                for value in values {
                    self.expression_stack
                        .push((value, Some(QueryExprParentType::Set)));
                }
            }
            QueryExpr::Record { pairs } => {
                for (_, value) in pairs {
                    self.expression_stack
                        .push((value, Some(QueryExprParentType::Record)));
                }
            }
            QueryExpr::RawSQL { args, .. } => {
                for arg in args {
                    self.expression_stack
                        .push((arg, Some(QueryExprParentType::RawSQL)));
                }
            }
        };
        Some((next_expr, parent))
    }
}

impl QueryExpr {
    // In-place mutation of subexpressions; walks from leaves to root (post-order)
    fn mut_subexpressions_helper(
        &mut self,
        parent: Option<QueryExprParentType>,
        f: &mut impl FnMut(&mut QueryExpr, Option<QueryExprParentType>),
    ) {
        match self {
            QueryExpr::Lit(_) => (),
            QueryExpr::Unknown { .. } => (),
            QueryExpr::If {
                test_expr,
                then_expr,
                else_expr,
            } => {
                test_expr.mut_subexpressions_helper(Some(QueryExprParentType::If), f);
                then_expr.mut_subexpressions_helper(Some(QueryExprParentType::If), f);
                else_expr.mut_subexpressions_helper(Some(QueryExprParentType::If), f);
            }
            QueryExpr::And { left, right } => {
                left.mut_subexpressions_helper(Some(QueryExprParentType::And), f);
                right.mut_subexpressions_helper(Some(QueryExprParentType::And), f);
            }
            QueryExpr::Or { left, right } => {
                left.mut_subexpressions_helper(Some(QueryExprParentType::Or), f);
                right.mut_subexpressions_helper(Some(QueryExprParentType::Or), f);
            }
            QueryExpr::UnaryApp { arg, op } => {
                arg.mut_subexpressions_helper(Some(QueryExprParentType::UnaryApp(*op)), f);
            }
            QueryExpr::BinaryApp { left, right, op } => {
                left.mut_subexpressions_helper(Some(QueryExprParentType::BinaryApp(*op)), f);
                right.mut_subexpressions_helper(Some(QueryExprParentType::BinaryApp(*op)), f);
            }
            QueryExpr::MulByConst { arg, .. } => {
                arg.mut_subexpressions_helper(Some(QueryExprParentType::MulByConst), f);
            }
            QueryExpr::GetAttrRecord { expr, .. } => {
                expr.mut_subexpressions_helper(Some(QueryExprParentType::GetAttrRecord), f);
            }
            QueryExpr::GetAttrEntity { expr, .. } => {
                expr.mut_subexpressions_helper(Some(QueryExprParentType::GetAttrEntity), f);
            }
            QueryExpr::InEntity { left, right, .. } => {
                left.mut_subexpressions_helper(Some(QueryExprParentType::InEntity), f);
                right.mut_subexpressions_helper(Some(QueryExprParentType::InEntity), f);
            }
            QueryExpr::InSet { left, right, .. } => {
                left.mut_subexpressions_helper(Some(QueryExprParentType::InSet), f);
                right.mut_subexpressions_helper(Some(QueryExprParentType::InSet), f);
            }
            QueryExpr::HasAttrRecord { expr, .. } => {
                expr.mut_subexpressions_helper(Some(QueryExprParentType::HasAttrRecord), f);
            }
            QueryExpr::IsNotNull(arg) => {
                arg.mut_subexpressions_helper(Some(QueryExprParentType::IsNotNull), f);
            }
            QueryExpr::Like { expr, .. } => {
                expr.mut_subexpressions_helper(Some(QueryExprParentType::Like), f);
            }
            QueryExpr::Set(values) => {
                for v in values {
                    v.mut_subexpressions_helper(Some(QueryExprParentType::Set), f);
                }
            }
            QueryExpr::Record { pairs } => {
                for (_, v) in pairs {
                    v.mut_subexpressions_helper(Some(QueryExprParentType::Record), f);
                }
            }
            QueryExpr::RawSQL { args, .. } => {
                for arg in args {
                    arg.mut_subexpressions_helper(Some(QueryExprParentType::RawSQL), f);
                }
            }
        }
        f(self, parent);
    }

    pub fn mut_subexpressions(
        &mut self,
        f: &mut impl FnMut(&mut QueryExpr, Option<QueryExprParentType>),
    ) {
        self.mut_subexpressions_helper(None, f);
    }
}
