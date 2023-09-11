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

//! We provide immutable and mutable iterators over the subexpressions of a QueryExpr.
use cedar_policy_core::ast::{BinaryOp, UnaryOp};

use crate::query_expr::QueryExpr;

/// Immutable iterator over the subexpressions of a QueryExpr.
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

/// The type of a query expression
/// We use this specifically to track the parent type of a subexpression
/// when we create a subexpression iterator
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum QueryExprParentType {
    /// If expression
    If,
    /// And expression
    And,
    /// Or expression
    Or,
    /// Unary application
    UnaryApp(UnaryOp),
    /// Binary application
    BinaryApp(BinaryOp),
    /// Multiplication by constant
    MulByConst,
    /// In entity
    InEntity,
    /// In set
    InSet,
    /// Get attribute from entity
    GetAttrEntity,
    /// Get attribute from record
    GetAttrRecord,
    /// Has attribute from record
    HasAttrRecord,
    /// Is not null
    IsNotNull,
    /// Like
    Like,
    /// Set
    Set,
    /// Record
    Record,
    /// Raw SQL
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

    /// Iterate over the subexpressions of a query expression
    /// in post-order (from leaves to root)
    /// and apply a function to each subexpression
    pub fn mut_subexpressions(
        &mut self,
        f: &mut impl FnMut(&mut QueryExpr, Option<QueryExprParentType>),
    ) {
        self.mut_subexpressions_helper(None, f);
    }
}
