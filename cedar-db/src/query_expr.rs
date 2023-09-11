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

//! The QueryExpr IR is an intermediate representation as we compile Cedar expressions to
//! SQL queries. We try to only include features that are easy to convert to SQL, and we focus
//! especially on Postgresql while still trying to abstract away the features that are too specific
//! to Postgres.
//!
//! In particular, we have the following changes from Cedar:
//!     - We do not support sets. Instead, we use arrays to represent sets.
//!     - Because of this, we have a restricted equality operator. Certain types (e.g. nested sets) are not comparable.
//!     - All ambiguous functions are annotated with their types (e.g. `GetAttr`
//!         splits into `GetAttrEntity` or `GetAttrRecord` depending on the type, and
//!         each is annotated with the type of the entity/type of the record field).
//!     - We do not support `HasAttr` on entities. Instead, we use `IsNotNull` on the result of `GetAttrEntity`.
//!     - We do not currently support extension functions, except for `rawsql` which is handled as a special case.
use std::collections::{HashMap, HashSet};

use cedar_policy::EntityTypeName;
use cedar_policy_core::{
    ast::{BinaryOp, EntityType, Expr, ExprKind, Literal, Name, Pattern, SlotId, UnaryOp, Var},
    entities::SchemaType,
};
use cedar_policy_validator::{
    types::{EntityLUB, EntityRecordKind, OpenTag, Primitive, Type},
    TypeError,
};
use ref_cast::RefCast;
use smol_str::SmolStr;
use thiserror::Error;

use crate::query_expr_iterator::{QueryExprIterator, QueryExprParentType};

/// Errors that can occur when converting a Cedar expression to a QueryExpr
#[derive(Debug, Error, PartialEq, Eq)]
pub enum QueryExprError {
    /// This error occurs when a variable appears in the expression. This should never occur after partial evaluation.
    #[error("Variable {0} appears in the expression. Consider doing partial evaluation first.")]
    VariableAppears(Var),

    /// This error occurs when a slot appears in the expression. This should never occur on non-template policies after partial evaluation.
    #[error("Slot {0} appears in the expression. Consider instantiating the policy first.")]
    SlotAppears(SlotId),

    /// This error occurs when an unknown is not annotated with its type. We need to keep track of what the unknown's type is
    /// so that we know which table its attributes come from, if we need to fetch its attributes.
    #[error("Unknown {0} is not annotated with a type.")]
    UnknownNotAnnotated(SmolStr),

    /// Extension functions are not currently supported.
    #[error("Found extension function call {0}. Extension functions are not currently supported.")]
    ExtensionFunctionAppears(Name),

    /// `rawsql`'s first argument must be an unknown named __RAWSQL. This may change in the future
    /// It is currently a workaround so that the Cedar partial evaluation engine does not try to evaluate raw sql.
    #[error("Extension function `rawsql` called with unknown named {0}; name should be __RAWSQL")]
    RawSQLFirstArgIncorrect(SmolStr),

    /// `rawsql`'s first argument must be an unknown named __RAWSQL. This may change in the future
    /// It is currently a workaround so that the Cedar partial evaluation engine does not try to evaluate raw sql.
    #[error("Extension function `rawsql` not called with unknown as first argument")]
    RawSQLFirstArgNotUnknown,

    /// `rawsql`'s argument cannot be an expression. Instead it should be a string literal.
    #[error("Cannot construct dynamic SQL queries")]
    RawSQLDynamic,

    /// This error occurs when a type annotation is `None`. This should never occur after successful typechecking.
    #[error("Typecheck error: Type annotation `None` on expression.")]
    TypeAnnotationNone,

    /// This error occurs when there is a validation error. It is not thrown by the query translator itself, which does not validate,
    /// but by `translate_expr` which does validation before calling the query translator.
    #[error("Validation error: the following type errors occured during strict validation: {0:?}")]
    ValidationError(Vec<TypeError>),

    /// This error occurs when during translation, there is a type error that should never occur on a correctly validated
    /// Cedar expression. This should never occur after successful typechecking.
    #[error("Type error: does not have correctly inferred types. Make sure to do strict validation (`typecheck` or `strict_transform`) before conversion.")]
    TypecheckError,

    /// This error occurs when subexpression can be multiple entity types. This should never occur after successful strict validation.
    #[error("Cannot get attribute when the type of the entity is not one particular entity. You can reduce if statements to ensure that no expression can be multiple different entity types.")]
    GetAttrLUBNotSingle,

    /// This error occurs when a QueryExpr is not attr-reduced and is converted to a QueryBuilder.
    /// A QueryExpr is attr_reduced when the argument to each GetAttryEntity is an entity-typed unknowns,
    /// and this is the only location where entity-typed unknowns appear.
    /// This error is thrown when an unknown appears in the expression that is not an argument to GetAttrEntity.
    #[error("Not attr-reduced. Entity deref unknown {0} found but not as argument of GetAttrEntity. Consider calling `reduce_attrs()`.")]
    NotAttrReduced(SmolStr),

    /// This error occurs when a QueryExpr is not attr-reduced and is converted to a QueryBuilder.
    /// A QueryExpr is attr_reduced when the argument to each GetAttryEntity is an entity-typed unknowns,
    /// and this is the only location where entity-typed unknowns appear.
    /// This error is thrown when the argument to a GetAttrEntity is not an entity-typed unknown.
    #[error("Not attr-reduced. Argument of GetAttrEntity is not an entity deref unknown. Consider calling `reduce_attrs()`.")]
    NotAttrReducedGetAttrEntity,

    /// This error occurs when an intermediate expression is a nested set.
    #[error("Nested sets are not supported.")]
    NestedSetsError,

    /// This error occurs when a comparison is made between two incomparable types (e.g. records containing sets).
    #[error("Incomparable types: comparing sets or comparing records with incomparable values is not supprted")]
    IncomparableTypes,

    /// Action attributes are not supported. This should never occur after partial evaluation since action attributes are always known statically
    #[error("Cannot convert action {action} attributes to SQL (getting attribute {attr})")]
    ActionAttribute {
        /// The action name
        action: Name,
        /// The attribute name that was attempted to be accessed
        attr: SmolStr
    },

    /// This error occurs when an action type appears in the expression
    #[error("Action hierarchy is not supported for conversion to SQL (on action {0})")]
    ActionTypeAppears(Name),
}

type Result<T> = std::result::Result<T, QueryExprError>;

/// This is the type information needed to cast a non-set Cedar value to a non-array SQL value
/// Note that `String` and `EntityId` are unified because both are represented as SQL strings
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QueryPrimitiveType {
    /// Boolean type
    Bool,
    /// Long type
    Long,
    /// String or EntityId type (both are represented as strings)
    StringOrEntity,
    /// Record type (represented as Postgres json)
    Record,
}

/// The type of values and expressions in the QueryExpr IR
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QueryType {
    /// A primitive (non-array) type, which includes bools, longs, strings, entity ids, and records
    Primitive(QueryPrimitiveType),
    /// An array of primitives. Note that we do not supported nested sets/nested arrays.
    Array(QueryPrimitiveType),
}

impl QueryType {
    /// Returns the primitive type of this array QueryType. If it is already a primitive type, just returns itself
    pub fn get_type(self) -> QueryPrimitiveType {
        match self {
            QueryType::Primitive(t) => t,
            QueryType::Array(t) => t,
        }
    }

    /// Convert a primitive type to an array of this primitive type.
    /// If this is already an array, it returns an error.
    pub fn promote(self) -> Result<Self> {
        match self {
            QueryType::Primitive(t) => Ok(QueryType::Array(t)),
            QueryType::Array(_) => Err(QueryExprError::NestedSetsError),
        }
    }
}

impl From<QueryPrimitiveType> for QueryType {
    fn from(tp: QueryPrimitiveType) -> Self {
        QueryType::Primitive(tp)
    }
}

impl TryFrom<&Type> for QueryType {
    type Error = QueryExprError;

    fn try_from(value: &Type) -> Result<Self> {
        match value {
            Type::Never
            | Type::True
            | Type::False
            | Type::Primitive {
                primitive_type: Primitive::Bool,
            } => Ok(QueryPrimitiveType::Bool.into()),
            Type::Primitive {
                primitive_type: Primitive::Long,
            } => Ok(QueryPrimitiveType::Long.into()),
            Type::Primitive {
                primitive_type: Primitive::String,
            } => Ok(QueryPrimitiveType::StringOrEntity.into()),
            Type::Set { element_type } => {
                let inner_result: QueryType = element_type
                    .as_deref()
                    .ok_or(QueryExprError::TypeAnnotationNone)?
                    .try_into()?;
                inner_result.promote()
            }
            Type::EntityOrRecord(EntityRecordKind::Record { .. }) => {
                Ok(QueryPrimitiveType::Record.into())
            }
            Type::EntityOrRecord(_) => Ok(QueryPrimitiveType::StringOrEntity.into()),
            Type::ExtensionType { name } => {
                Err(QueryExprError::ExtensionFunctionAppears(name.to_owned()))
            }
        }
    }
}

fn entity_lub_to_typename(lub: &EntityLUB) -> Result<&EntityTypeName> {
    lub.get_single_entity()
        .ok_or(QueryExprError::GetAttrLUBNotSingle)
        .map( EntityTypeName::ref_cast)
}

fn type_to_entity_typename(tp: Option<&Type>) -> Result<&EntityTypeName> {
    match tp.ok_or(QueryExprError::TypeAnnotationNone)? {
        Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => entity_lub_to_typename(lub),
        Type::EntityOrRecord(EntityRecordKind::ActionEntity { name, .. }) => {
            Err(QueryExprError::ActionTypeAppears(name.clone()))
        }
        _ => Err(QueryExprError::TypecheckError),
    }
}

/// The kind of attribute that can be retrieved from an entity.
/// It is either an attribute or the id of the entity.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AttrOrId {
    /// Retrieve the attribute with this name
    Attr(SmolStr),
    /// This attribute is the ID of the entity
    /// We keep track of what the corresponding column name in the actual SQL table will be
    Id(SmolStr),
}

/// This is a Cedar expression intended to be more easily converted into a SQL query.
/// It refines the Cedar expression language by specifying the types of
/// `GetAttr` and `HasAttr`. Here, `U` is the type of unknowns
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum QueryExpr {
    /// A literal value
    Lit(Literal),
    // Skipped: Var, Slot; these should be removed by partial evaluation/policy instantiation
    /// An unknown value
    Unknown(UnknownType),
    /// An if expression
    If {
        /// The condition
        test_expr: Box<QueryExpr>,
        /// The then branch if the condition is true
        then_expr: Box<QueryExpr>,
        /// The else branch if the condition is false
        else_expr: Box<QueryExpr>,
    },
    /// A logical and expression
    And {
        /// The left operand of the and
        left: Box<QueryExpr>,
        /// The right operand of the and
        right: Box<QueryExpr>,
    },
    /// A logical or expression
    Or {
        /// The left operand of the or
        left: Box<QueryExpr>,
        /// The right operand of the or
        right: Box<QueryExpr>,
    },
    /// A unary application of a unary operator
    UnaryApp {
        /// The unary operator
        op: UnaryOp,
        /// The argument to the unary operator
        arg: Box<QueryExpr>,
    },
    /// A binary application of a binary operator
    BinaryApp {
        /// The binary operator; note that `in` is not allowed here (it is handled as a special case)
        op: BinaryOp,
        /// The left operand of the binary operator
        left: Box<QueryExpr>,
        /// The right operand of the binary operator
        right: Box<QueryExpr>,
    },
    /// An `in` expression where the RHS is an entity.
    /// This is handled as a special case because we want to keep track of the entity types
    /// of the left and right operands.
    /// Note: the semantics of `in` for QueryExpr do not include reflexivity, so `x in x` is not necessarily true.
    InEntity {
        /// The left operand of the `in` expression
        left: Box<QueryExpr>,
        /// The right operand of the `in` expression
        right: Box<QueryExpr>,
        /// The entity type of the left operand
        left_type: EntityTypeName,
        /// The entity type of the right operand
        right_type: EntityTypeName,
    },
    /// An `in` expression where the RHS is a set.
    /// This is handled as a special case because we want to keep track of the entity types
    /// of the left and right operands.
    /// Note: the semantics of `in` for QueryExpr do not include reflexivity, so `x inSet [x]` is not necessarily true.
    InSet {
        /// The left operand of the `in` expression
        left: Box<QueryExpr>,
        /// The right operand of the `in` expression
        right: Box<QueryExpr>,
        /// The entity type of the left operand
        left_type: EntityTypeName,
        /// The entity type of the elements of the right operand
        right_type: EntityTypeName,
    },
    /// A multiplication by a constant
    MulByConst {
        /// The argument to the multiplication
        arg: Box<QueryExpr>,
        /// The constant to multiply by
        constant: i64,
    },
    /// A get attribute expression on an entity
    GetAttrEntity {
        /// The entity to get the attribute from
        expr: Box<QueryExpr>,
        /// The type of the entity
        expr_type: EntityTypeName,
        /// The attribute to get (could be the id of the entity)
        attr: AttrOrId,
    },
    /// A get attribute expression on a record
    GetAttrRecord {
        /// The record to get the attribute from
        expr: Box<QueryExpr>,
        /// The name of the attribute to get
        attr: SmolStr,
        /// The type of the result of the expression. We need to know the result type because
        /// in implementations, after retrieving a JSON field, the resulting type will be "json"
        /// by default and we need to cast it explicitly
        result_type: QueryType,
    },
    /// A has attribute expression on a record
    HasAttrRecord {
        /// The record to check for the attribute
        expr: Box<QueryExpr>,
        /// The name of the attribute to check for
        attr: SmolStr,
    },
    /// The IS NOT NULL operation which returns true if the argument is not null.
    /// We use this in combination with GetAttrEntity instead of `HasAttr` on entities
    IsNotNull(Box<QueryExpr>),
    /// A comparison of an expression against a pattern
    Like {
        /// The expression to compare against the pattern
        expr: Box<QueryExpr>,
        /// The pattern to compare against
        pattern: Pattern,
    },
    /// The array constructor operation (despite being called Set, the QueryExpr IR uses arrays rather than sets)
    Set(Vec<QueryExpr>),
    /// The record constructor operation.
    Record {
        /// The attribute/value pairs of the record
        /// No attribute should be repeated (TODO: check this during conversion)
        pairs: Vec<(SmolStr, QueryExpr)>,
    },
    /// A raw SQL expression. This is used as an escape hatch and is how the `rawsql` extension
    /// function is handled.
    RawSQL {
        /// The SQL query string, which may include placeholders
        sql: SmolStr,
        /// The arguments to the SQL query string
        args: Vec<QueryExpr>,
    },
}

impl Default for QueryExpr {
    fn default() -> Self {
        QueryExpr::Lit(false.into())
    }
}

/// The result of checking whether two types are comparable for the purposes of equality, contains, containsAll, or containsAny
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComparableResult {
    /// The types are incomparable (e.g. records containing sets)
    Incomparable,
    /// The types are comparable by checking if each is a subset of the other
    /// This is only true for arrays of primitive types which are being compared for equality
    ComparableAsMutualContains,
    /// The types are comparable by directly checking if they are equal (e.g. primitives, records containing only primitives)
    ComparableAsEq,
}

impl ComparableResult {
    /// Convert this ComparableResult to one where ComparableAsMutualContains does not make sense
    /// by converting it to Incomparable
    pub fn must_be_eq(self) -> Self {
        match self {
            ComparableResult::ComparableAsEq => self,
            _ => ComparableResult::Incomparable,
        }
    }
}

impl QueryExpr {
    /// Given `left` and `right`, return the translation of `left in right`.
    /// Since `in` in QueryExpr is not necessarily reflexive, when `left` and `right` are of the same type
    /// the correct way to translate this is with left == right || left in right
    pub fn eq_or_in_entity(
        left: QueryExpr,
        right: QueryExpr,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    ) -> Self {
        let eq_expr = if left_type == right_type {
            Some(QueryExpr::BinaryApp {
                op: BinaryOp::Eq,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            })
        } else {
            None
        };
        let in_entity_expr = QueryExpr::InEntity {
            left: Box::new(left),
            right: Box::new(right),
            left_type,
            right_type,
        };
        match eq_expr {
            Some(eq_expr) => QueryExpr::Or {
                left: Box::new(eq_expr),
                right: Box::new(in_entity_expr),
            },
            None => in_entity_expr,
        }
    }

    /// Given `left` and `right`, return the translation of `left inSet right`.
    /// Since `inSet` in QueryExpr is not necessarily reflexive, when `left` and `right` are of the same type
    /// the correct way to translate this is with right.contains(left) || left inSet right
    pub fn contains_or_in_set(
        left: QueryExpr,
        right: QueryExpr,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    ) -> Self {
        let contains_expr = if left_type == right_type {
            Some(QueryExpr::BinaryApp {
                op: BinaryOp::Contains,
                left: Box::new(right.clone()),
                right: Box::new(left.clone()),
            })
        } else {
            None
        };
        let inset_expr = QueryExpr::InSet {
            left: Box::new(left),
            right: Box::new(right),
            left_type,
            right_type,
        };
        match contains_expr {
            Some(contains_expr) => QueryExpr::Or {
                left: Box::new(contains_expr),
                right: Box::new(inset_expr),
            },
            None => inset_expr,
        }
    }

    /// Returns true if types `t1` and `t2` are comparable using = in SQL
    /// The only disallowed comparable types are sets (which are still comparable by mutual contains if
    /// the element type is comparable by equals)
    /// and records which might contain something that cannot be compared by equals.
    /// This is because set equality requires sorting/some canonical order
    fn are_comparable(t1: &Type, t2: &Type) -> Result<ComparableResult> {
        match (t1, t2) {
            (
                Type::EntityOrRecord(EntityRecordKind::Record {
                    attrs,
                    open_attributes,
                }),
                Type::EntityOrRecord(EntityRecordKind::Record {
                    attrs: attrs2,
                    open_attributes: open_attributes2,
                }),
            ) => {
                if *open_attributes == OpenTag::OpenAttributes
                    || *open_attributes2 == OpenTag::OpenAttributes
                {
                    // Since the attributes are open, in particular the records may contain sets, so they are incomparable
                    Ok(ComparableResult::Incomparable)
                } else {
                    // We check the intersection of the two attributes
                    // since arrays will still be comparable with (missing)
                    for (k, v) in attrs.iter() {
                        if let Some(v2) = attrs2.get_attr(k) {
                            if QueryExpr::are_comparable(&v.attr_type, &v2.attr_type)?
                                != ComparableResult::ComparableAsEq
                            {
                                return Ok(ComparableResult::Incomparable);
                            }
                        }
                    }
                    Ok(ComparableResult::ComparableAsEq)
                }
            }
            (Type::Set { element_type: e1 }, Type::Set { element_type: e2 }) => {
                let e1 = e1.as_deref().ok_or(QueryExprError::TypeAnnotationNone)?;
                let e2 = e2.as_deref().ok_or(QueryExprError::TypeAnnotationNone)?;
                // If the inner elements are comparable as equals, then the sets are comparable as mutual contains
                if QueryExpr::are_comparable(e1, e2)? == ComparableResult::ComparableAsEq {
                    Ok(ComparableResult::ComparableAsMutualContains)
                } else {
                    Ok(ComparableResult::Incomparable)
                }
            }
            // All primitive types are comparable using ordinary equality
            _ => Ok(ComparableResult::ComparableAsEq),
        }
    }

    /// Returns true if types `t1` and `t2` are comparable using `op`
    /// Note: if op is not one of eq, contains, containsAll, or containsAny, always just returns
    /// ComparableAsEq. This allows treating ComparableAsEq as the catch-all for "just do the operation normally"
    fn are_op_comparable(op: BinaryOp, t1: &Type, t2: &Type) -> Result<ComparableResult> {
        match op {
            BinaryOp::Eq => QueryExpr::are_comparable(t1, t2),
            BinaryOp::Contains => match t1 {
                Type::Set { element_type } => Ok(QueryExpr::are_comparable(
                    t1,
                    element_type
                        .as_deref()
                        .ok_or(QueryExprError::TypeAnnotationNone)?,
                )?
                .must_be_eq()),
                _ => Err(QueryExprError::TypecheckError),
            },
            BinaryOp::ContainsAll | BinaryOp::ContainsAny => match (t1, t2) {
                (Type::Set { element_type: e1 }, Type::Set { element_type: e2 }) => {
                    let e1 = e1.as_deref().ok_or(QueryExprError::TypeAnnotationNone)?;
                    let e2 = e2.as_deref().ok_or(QueryExprError::TypeAnnotationNone)?;
                    Ok(QueryExpr::are_comparable(e1, e2)?.must_be_eq())
                }
                _ => Err(QueryExprError::TypecheckError),
            },
            _ => Ok(ComparableResult::ComparableAsEq),
        }
    }
}

impl TryFrom<&Expr<Option<Type>>> for QueryExpr {
    type Error = QueryExprError;

    fn try_from(value: &Expr<Option<Type>>) -> Result<Self> {
        match value.expr_kind() {
            ExprKind::Lit(l) => Ok(QueryExpr::Lit(l.to_owned())),
            ExprKind::Var(v) => Err(QueryExprError::VariableAppears(v.to_owned())),
            ExprKind::Slot(s) => Err(QueryExprError::SlotAppears(s.to_owned())),
            ExprKind::Unknown { .. } => {
                // PANIC SAFETY Doesn't panic because we know `value`'s constructor is `Unknown`
                #[allow(clippy::unwrap_used)]
                Ok(UnknownType::from_expr(value).unwrap().into())
            }
            ExprKind::If {
                test_expr,
                then_expr,
                else_expr,
            } => Ok(QueryExpr::If {
                test_expr: Box::new(QueryExpr::try_from(test_expr.as_ref())?),
                then_expr: Box::new(QueryExpr::try_from(then_expr.as_ref())?),
                else_expr: Box::new(QueryExpr::try_from(else_expr.as_ref())?),
            }),
            ExprKind::And { left, right } => Ok(QueryExpr::And {
                left: Box::new(QueryExpr::try_from(left.as_ref())?),
                right: Box::new(QueryExpr::try_from(right.as_ref())?),
            }),
            ExprKind::Or { left, right } => Ok(QueryExpr::Or {
                left: Box::new(QueryExpr::try_from(left.as_ref())?),
                right: Box::new(QueryExpr::try_from(right.as_ref())?),
            }),
            ExprKind::UnaryApp { op, arg } => Ok(QueryExpr::UnaryApp {
                op: *op,
                arg: Box::new(QueryExpr::try_from(arg.as_ref())?),
            }),
            ExprKind::BinaryApp { op, arg1, arg2 } => {
                if matches!(op, BinaryOp::In) {
                    let arg1_tp_entity = type_to_entity_typename(arg1.data().as_ref())?;
                    let arg2_tp = arg2
                        .data()
                        .as_ref()
                        .ok_or(QueryExprError::TypeAnnotationNone)?;
                    match arg2_tp {
                        Type::EntityOrRecord(_) => Ok(QueryExpr::eq_or_in_entity(
                            QueryExpr::try_from(arg1.as_ref())?,
                            QueryExpr::try_from(arg2.as_ref())?,
                            arg1_tp_entity.to_owned(),
                            type_to_entity_typename(Some(arg2_tp))?.to_owned(),
                        )),
                        Type::Set { element_type } => Ok(QueryExpr::contains_or_in_set(
                            QueryExpr::try_from(arg1.as_ref())?,
                            QueryExpr::try_from(arg2.as_ref())?,
                            arg1_tp_entity.to_owned(),
                            type_to_entity_typename(element_type.as_deref())?.to_owned(),
                        )),
                        _ => Err(QueryExprError::TypecheckError),
                    }
                } else {
                    match QueryExpr::are_op_comparable(
                        *op,
                        arg1.data()
                            .as_ref()
                            .ok_or(QueryExprError::TypeAnnotationNone)?,
                        arg2.data()
                            .as_ref()
                            .ok_or(QueryExprError::TypeAnnotationNone)?,
                    )? {
                        ComparableResult::Incomparable => Err(QueryExprError::IncomparableTypes),
                        ComparableResult::ComparableAsEq => Ok(QueryExpr::BinaryApp {
                            op: *op,
                            left: Box::new(QueryExpr::try_from(arg1.as_ref())?),
                            right: Box::new(QueryExpr::try_from(arg2.as_ref())?),
                        }),
                        ComparableResult::ComparableAsMutualContains => {
                            let left_query_expr = QueryExpr::try_from(arg1.as_ref())?;
                            let right_query_expr = QueryExpr::try_from(arg2.as_ref())?;
                            Ok(QueryExpr::And {
                                left: Box::new(QueryExpr::BinaryApp {
                                    op: BinaryOp::ContainsAll,
                                    left: Box::new(left_query_expr.clone()),
                                    right: Box::new(right_query_expr.clone()),
                                }),
                                right: Box::new(QueryExpr::BinaryApp {
                                    op: BinaryOp::ContainsAll,
                                    left: Box::new(right_query_expr),
                                    right: Box::new(left_query_expr),
                                }),
                            })
                        }
                    }
                }
            }
            ExprKind::MulByConst { arg, constant } => Ok(QueryExpr::MulByConst {
                arg: Box::new(QueryExpr::try_from(arg.as_ref())?),
                constant: *constant,
            }),
            ExprKind::ExtensionFunctionApp { fn_name, args } => {
                if fn_name.namespace() == "rawsql" {
                    let mut args_iter = args.iter();
                    // Ignore the first argument because it must be an unknown
                    match args_iter.next() {
                        Some(e) => match e.expr_kind() {
                            ExprKind::Unknown { name, .. } => {
                                if name != "__RAWSQL" {
                                    return Err(QueryExprError::RawSQLFirstArgIncorrect(
                                        name.to_owned(),
                                    ));
                                }
                            }
                            _ => return Err(QueryExprError::RawSQLFirstArgNotUnknown),
                        },
                        _ => return Err(QueryExprError::RawSQLFirstArgNotUnknown),
                    };
                    let sql = match args_iter.next() {
                        Some(e) => match e.expr_kind() {
                            ExprKind::Lit(Literal::String(s)) => s.to_owned(),
                            _ => return Err(QueryExprError::RawSQLDynamic),
                        },
                        _ => return Err(QueryExprError::TypecheckError),
                    };
                    let args = args_iter
                        .map(QueryExpr::try_from)
                        .collect::<Result<Vec<_>>>()?;
                    Ok(QueryExpr::RawSQL { sql, args })
                } else {
                    Err(QueryExprError::ExtensionFunctionAppears(fn_name.to_owned()))
                }
            }
            ExprKind::GetAttr { expr, attr } => {
                let expr_tp = expr
                    .data()
                    .as_ref()
                    .ok_or(QueryExprError::TypeAnnotationNone)?;
                match expr_tp {
                    Type::EntityOrRecord(EntityRecordKind::Record { .. }) => {
                        Ok(QueryExpr::GetAttrRecord {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            attr: attr.to_owned(),
                            result_type: value
                                .data()
                                .as_ref()
                                .ok_or(QueryExprError::TypeAnnotationNone)?
                                .try_into()?,
                        })
                    }
                    Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => {
                        Ok(QueryExpr::GetAttrEntity {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            expr_type: entity_lub_to_typename(lub)?.to_owned(),
                            attr: AttrOrId::Attr(attr.to_owned()),
                        })
                    }
                    Type::EntityOrRecord(EntityRecordKind::ActionEntity { name, .. }) => {
                        Err(QueryExprError::ActionAttribute {
                            action: name.clone(),
                            attr: attr.clone(),
                        })
                    }
                    _ => Err(QueryExprError::TypecheckError),
                }
            }
            ExprKind::HasAttr { expr, attr } => {
                let expr_tp = expr
                    .data()
                    .as_ref()
                    .ok_or(QueryExprError::TypeAnnotationNone)?;
                match expr_tp {
                    Type::EntityOrRecord(EntityRecordKind::Record { .. }) => {
                        Ok(QueryExpr::HasAttrRecord {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            attr: attr.to_owned(),
                        })
                    }
                    Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => {
                        Ok(QueryExpr::IsNotNull(Box::new(QueryExpr::GetAttrEntity {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            expr_type: entity_lub_to_typename(lub)?.to_owned(),
                            attr: AttrOrId::Attr(attr.to_owned()),
                        })))
                    }
                    Type::EntityOrRecord(EntityRecordKind::ActionEntity { name, .. }) => {
                        Err(QueryExprError::ActionAttribute {
                            action: name.clone(),
                            attr: attr.clone(),
                        })
                    }
                    _ => Err(QueryExprError::TypecheckError),
                }
            }
            ExprKind::Like { expr, pattern } => Ok(QueryExpr::Like {
                expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                pattern: pattern.to_owned(),
            }),
            ExprKind::Set(s) => {
                QueryType::try_from(
                    value
                        .data()
                        .as_ref()
                        .ok_or(QueryExprError::TypeAnnotationNone)?,
                )?;
                Ok(QueryExpr::Set(
                    s.iter()
                        .map(QueryExpr::try_from)
                        .collect::<Result<Vec<_>>>()?,
                ))
            }
            ExprKind::Record { pairs } => Ok(QueryExpr::Record {
                pairs: pairs
                    .iter()
                    .map(|(k, v)| Ok((k.to_owned(), QueryExpr::try_from(v)?)))
                    .collect::<Result<Vec<_>>>()?,
            }),
        }
    }
}

/// The default unknown type for a query expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnknownType {
    /// An unknown entity
    EntityType {
        /// The type of the entity
        ty: EntityTypeName,
        /// The name of the unknown
        name: SmolStr,
    },
    /// Escape hatch for non-entity variables
    /// These are not handled in any special way. They are just passed through to the SQL query as variables.
    /// TODO: perhaps replace this with `rawsql` as the (only) escape hatch?
    NonEntityType {
        /// This will turn into the table name if it is provided
        /// TODO: should we allow this to be a sea query TableRef instead?
        pfx: Option<SmolStr>,
        /// The name of the unknown
        name: SmolStr,
    },
}

impl UnknownType {
    /// Create an unknown type from a name and entity type
    /// If the entity type is provided, this will become a regular UnknownType::EntityType
    /// Otherwise, it will be one of the "escape hatch" type unknown types.
    pub fn of_name_and_type(name: SmolStr, ty: Option<EntityTypeName>) -> Self {
        match ty {
            Some(ty) => UnknownType::EntityType { ty, name },
            None => UnknownType::NonEntityType { pfx: None, name },
        }
    }

    /// Get the name of this unknown
    pub fn get_name(&self) -> &str {
        match self {
            UnknownType::EntityType { name, .. } => name,
            UnknownType::NonEntityType { name, .. } => name,
        }
    }

    /// Get the prefix of this escape-hatch unknown if it exists
    pub fn get_pfx(&self) -> Option<&str> {
        match self {
            UnknownType::NonEntityType { pfx: Some(pfx), .. } => Some(pfx.as_str()),
            _ => None,
        }
    }

    /// Helper function to convert an expression into an unknown
    /// Used in the conversion and also to collect free variables
    pub fn from_expr<T>(e: &Expr<T>) -> Option<Self> {
        match e.expr_kind() {
            ExprKind::Unknown {
                name,
                type_annotation,
            } => Some(UnknownType::of_name_and_type(
                name.to_owned(),
                match type_annotation {
                    Some(SchemaType::Entity {
                        ty: EntityType::Concrete(n),
                    }) => Some(EntityTypeName::ref_cast(n).to_owned()),
                    _ => None,
                },
            )),
            _ => None,
        }
    }
}

impl From<UnknownType> for QueryExpr {
    fn from(u: UnknownType) -> Self {
        QueryExpr::Unknown(u)
    }
}

impl QueryExpr {
    /// Get an iterator of all the subexpressions of this QueryExpr
    /// Along with each subexpression is the type of the parent node of the subexpression,
    /// or None if the subexpression was the root node.
    pub fn subexpressions_with_parents(
        &self,
    ) -> impl Iterator<Item = (&QueryExpr, Option<QueryExprParentType>)> {
        QueryExprIterator::new(self)
    }

    /// Get all the subexpressions of this QueryExpr
    pub fn subexpressions(&self) -> impl Iterator<Item = &QueryExpr> {
        self.subexpressions_with_parents().map(|(e, _)| e)
    }

    /// Retrieve all the unknowns in the QueryExpr
    pub fn get_unknowns(&self) -> impl Iterator<Item = &UnknownType> {
        self.subexpressions().filter_map(|e| match e {
            QueryExpr::Unknown(u) => Some(u),
            _ => None,
        })
    }
}

/// The type of a QueryExpr along with the free variables from the original expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QueryExprWithVars {
    /// The QueryExpr itself
    pub(crate) expr: QueryExpr,
    /// The set of unknowns in the *original* expression
    /// We guarantee that the unknowns in the expression are a subset of this set
    pub(crate) vars: Vec<UnknownType>,
}

impl QueryExprWithVars {
    /// Create a QueryExprWithVars from an expression and a set of free variables
    pub fn from_expr(e: &Expr<Option<Type>>, vars: Vec<UnknownType>) -> Result<Self> {
        Ok(QueryExprWithVars {
            expr: QueryExpr::try_from(e)?,
            vars,
        })
    }

    /// Rename all the variables in the given QueryExpr
    pub fn rename(&mut self, map: impl Fn(&mut UnknownType)) {
        self.expr.rename(&map);
        for v in &mut self.vars {
            map(v);
        }
    }

    /// Rename all the attributes in the given QueryExpr
    pub fn rename_attrs(&mut self, map: impl Fn(&EntityTypeName, &mut AttrOrId)) {
        self.expr.rename_attrs(map);
    }
}

/// A BindingValue is the LHS in a "let" expression, containing the unknown name and type
/// as well as the order that this binding was introduced in the query
#[derive(Debug, Clone)]
pub struct BindingValue {
    insertion_order: usize,
    pub(crate) name: SmolStr,
    pub(crate) ty: EntityTypeName,
}

impl BindingValue {
    /// Convert this BindingValue into an UnknownType
    pub fn into_unknown(self) -> UnknownType {
        UnknownType::EntityType {
            ty: self.ty,
            name: self.name,
        }
    }
}

/// Used to construct bindings -- we keep the expressions in a
/// hash map so that duplicate expressions are not introduced to separate bindings
/// but also remember the insertion order
#[derive(Debug, Clone, Default)]
pub struct BindingsBuilder {
    bindings: HashMap<Box<QueryExpr>, BindingValue>,
}

/// A sequence of let bindings. Each binding consists of a BindingValue, which includes the name
/// and type of the unknown, and the expression that the unknown is bound to.
#[derive(Debug, Clone, Default)]
pub struct Bindings(Vec<(BindingValue, Box<QueryExpr>)>);

impl Bindings {
    /// Get an iterator through the bindings
    pub fn iter(&self) -> impl Iterator<Item = (&BindingValue, &QueryExpr)> {
        self.0.iter().map(|(bv, qe)| (bv, qe.as_ref()))
    }

    /// Get a mutable iterator through the bindings
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&mut BindingValue, &mut QueryExpr)> {
        self.0.iter_mut().map(|(bv, qe)| (bv, qe.as_mut()))
    }
}

impl BindingsBuilder {
    /// Build the bindings
    pub fn build(self) -> Bindings {
        let mut result: Vec<_> = self.bindings.into_iter().map(|(k, v)| (v, k)).collect();
        result.sort_by(|(a, _), (b, _)| a.insertion_order.cmp(&b.insertion_order));
        Bindings(result)
    }

    /// Insert a new binding into the bindings
    pub fn insert(
        &mut self,
        q: Box<QueryExpr>,
        ty: EntityTypeName,
        id_gen: &mut IdGen,
    ) -> BindingValue {
        let size = self.bindings.len();
        self.bindings
            .entry(q)
            .or_insert_with(|| BindingValue {
                name: id_gen.gen_id(),
                ty,
                insertion_order: size,
            })
            .clone()
    }
}

/// A sequence of let bindings followed by an expression.
#[derive(Debug, Clone)]
pub struct ExprWithBindings {
    pub(crate) bindings: Bindings,
    pub(crate) expr: Box<QueryExpr>,
    /// all the free variables in the original expression
    free_vars: HashSet<UnknownType>,
}

impl From<QueryExpr> for ExprWithBindings {
    fn from(expr: QueryExpr) -> Self {
        ExprWithBindings {
            bindings: Bindings::default(),
            free_vars: expr.get_unknowns().cloned().collect(),
            expr: Box::new(expr),
        }
    }
}

impl From<QueryExprWithVars> for ExprWithBindings {
    fn from(value: QueryExprWithVars) -> Self {
        ExprWithBindings {
            bindings: Bindings::default(),
            free_vars: value.vars.into_iter().collect(),
            expr: Box::new(value.expr),
        }
    }
}

/// This is used to generate ids for a query expression, which is in turn
/// used to name the temporary tables that are created when `GetAttrEntity` are turned into
/// bindings.
#[derive(Debug, Clone, Copy, Default)]
pub struct IdGen {
    next_id: usize,
}

/// The prefix used for temporary table names
const ID_GEN_PREFIX: &str = "temp__";

impl IdGen {
    /// Create a new IdGen
    pub fn new() -> Self {
        IdGen { next_id: 0 }
    }

    /// Avoid generating ids that are already in use in the given query expression
    /// We do this by simply incrementing `next_id` to a value large enough that it is not in use
    /// This incrementing only occurs if an unknown name starts with the ID_GEN_PREFIX
    pub fn avoid_unknowns_in(&mut self, e: &QueryExpr) -> &mut Self {
        for unk in e.get_unknowns() {
            let name = unk.get_name();
            if let Some(stripped) = name.strip_prefix(ID_GEN_PREFIX) {
                if let Ok(id) = stripped.parse::<usize>() {
                    self.next_id = self.next_id.max(id + 1);
                }
            }
        }
        self
    }

    /// Generate a new id and increment the internal id counter so that this id is not generated again
    pub fn gen_id(&mut self) -> SmolStr {
        let id = self.next_id;
        self.next_id += 1;
        SmolStr::new(format!("{}{}", ID_GEN_PREFIX, id))
    }
}

impl QueryExpr {
    /// An expression is said to be attr-reduced when the only
    /// expressions that appear on the left argument of a `GetAttrEntity` are of the form `Unknown(EntityType(_))`
    /// This function turns the expression into an attr-reduced form.
    pub fn reduce_attrs(&mut self, id_gen: &mut IdGen) -> Bindings {
        let mut builder = BindingsBuilder::default();
        self.mut_subexpressions(&mut |expr, _| {
            if let QueryExpr::GetAttrEntity {
                expr, expr_type, ..
            } = expr
            {
                if expr.is_unknown_entity_deref() {
                    // if it is already attr-reduced, skip
                    return;
                }

                let expr_owned = std::mem::take(expr);
                let bv = builder.insert(expr_owned, expr_type.clone(), id_gen);
                *expr = Box::new(bv.into_unknown().into());
            }
        });

        let mut bindings = builder.build();

        for (_, e) in bindings.iter_mut() {
            e.unreduce_unknowns();
        }
        self.unreduce_unknowns();

        bindings
    }

    /// Add ".uid" to the ends of entities that are being used as strings
    fn unreduce_unknowns(&mut self) {
        self.mut_subexpressions(&mut |expr, parent| {
            if parent != Some(QueryExprParentType::GetAttrEntity) {
                if let Some(tp) = expr.get_unknown_entity_type() {
                    *expr = QueryExpr::GetAttrEntity {
                        expr: Box::new(expr.clone()),
                        expr_type: tp.clone(),
                        attr: AttrOrId::Id("uid".into()), // we use a default id value of "uid"
                    };
                }
            }
        });
    }

    /// Rename all the unknowns in this expression using the given map.
    /// Any unknowns which are not keys in the map are left alone
    pub fn rename(&mut self, map: impl Fn(&mut UnknownType)) {
        self.mut_subexpressions(&mut |expr, _| {
            if let QueryExpr::Unknown(u) = expr {
                map(u);
            }
        });
    }

    /// Rename all the attributes in this expression using the given map.
    pub fn rename_attrs(&mut self, map: impl Fn(&EntityTypeName, &mut AttrOrId)) {
        self.mut_subexpressions(&mut |expr, _| {
            if let QueryExpr::GetAttrEntity {
                attr, expr_type, ..
            } = expr
            {
                map(expr_type, attr);
            }
        });
    }

    /// If this expression is of the form `Unknown(EntityType(s))`, return `Some(s)`.
    /// In reduced-attr form, this should succeed on all arguments of GetAttrEntity.
    pub fn get_unknown_entity_deref_name(&self) -> Option<SmolStr> {
        match self {
            QueryExpr::Unknown(UnknownType::EntityType { name, .. }) => Some(name.clone()),
            _ => None,
        }
    }

    /// If this expression is of the form `Unknown(EntityType(s))`, return `Some(s)`.
    pub fn get_unknown_entity_type(&self) -> Option<&EntityTypeName> {
        match self {
            QueryExpr::Unknown(UnknownType::EntityType { ty, .. }) => Some(ty),
            _ => None,
        }
    }

    /// Equivalent to `self.get_unknown_entity_deref_name().is_some()`
    pub fn is_unknown_entity_deref(&self) -> bool {
        matches!(self, QueryExpr::Unknown(UnknownType::EntityType { .. }))
    }
}

impl ExprWithBindings {
    /// Turn the expression with bindings into an attr-reduced form.
    pub fn reduce_attrs(&mut self) {
        let mut id_gen = IdGen::new();
        id_gen.avoid_unknowns_in(self.expr.as_ref());
        self.bindings = self.expr.reduce_attrs(&mut id_gen);
    }

    /// Get all the free variables
    pub fn get_free_vars(&self) -> &HashSet<UnknownType> {
        &self.free_vars
    }
}
