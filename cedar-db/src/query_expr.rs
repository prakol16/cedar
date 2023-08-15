use std::collections::HashMap;

use cedar_policy::EntityTypeName;
use cedar_policy_core::ast::{Expr, Literal, UnaryOp, BinaryOp, Pattern, ExprKind, SlotId, Var, Name};
use cedar_policy_validator::types::{Type, Primitive, EntityRecordKind, EntityLUB};
use ref_cast::RefCast;
use smol_str::SmolStr;
use thiserror::Error;


#[derive(Debug, Error)]
pub enum QueryExprError {
    #[error("Variable {0} appears in the expression. Consider calling `partial_eval` first.")]
    VariableAppears(Var),
    #[error("Slot {0} appears in the expression. Consider instantiating the policy first.")]
    SlotAppears(SlotId),
    #[error("Unknown {0} is not annotated with a type.")]
    UnknownNotAnnotated(SmolStr),
    #[error("Found extension function call {0}. Extension functions are not currently supported.")]
    ExtensionFunctionAppears(Name),
    #[error("Typecheck error: Type annotation `None` on expression.")]
    TypeAnnotationNone,
    #[error("Type error: does not have correctly inferred types. Make sure to do `typecheck` or `strict_transform` before calling this function.")]
    TypecheckError,
    #[error("Cannot get attribute when the type of the entity is not one particular entity. You can reduce if statements to ensure that no expression can be multiple different entity types.")]
    GetAttrLUBNotSingle,
    #[error("Not attr-reduced. Entity deref unknown {0} found but not as argument of GetAttrEntity. Consider calling `reduce_attrs()`.")]
    NotAttrReduced(SmolStr),
    #[error("Not attr-reduced. Argument of GetAttrEntity is not an entity deref unknown. Consider calling `reduce_attrs()`.")]
    NotAttrReducedGetAttrEntity,
}

type Result<T> = std::result::Result<T, QueryExprError>;


// This is the type information needed to cast a Cedar value to an SQL value
// Note that `String` and `EntityId` are unified because both are represented as SQL strings
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastableType {
    Bool,
    Long,
    StringOrEntity,
    Set,
    Record,
}

impl TryFrom<&Type> for CastableType {
    type Error = QueryExprError;

    fn try_from(value: &Type) -> Result<Self> {
        match value {
            Type::Never | Type::True | Type::False | Type::Primitive { primitive_type: Primitive::Bool } => Ok(CastableType::Bool),
            Type::Primitive { primitive_type: Primitive::Long } => Ok(CastableType::Long),
            Type::Primitive { primitive_type: Primitive::String } => Ok(CastableType::StringOrEntity),
            Type::Set { .. } => Ok(CastableType::Set),
            Type::EntityOrRecord(EntityRecordKind::Record { .. }) => Ok(CastableType::Record),
            Type::EntityOrRecord(_) => Ok(CastableType::StringOrEntity),
            Type::ExtensionType { name } => Err(QueryExprError::ExtensionFunctionAppears(name.to_owned())),
        }
    }
}

fn entity_lub_to_typename(lub: &EntityLUB) -> Result<&EntityTypeName> {
    lub.get_single_entity().ok_or(QueryExprError::GetAttrLUBNotSingle).map(|e| EntityTypeName::ref_cast(e))
}

fn type_to_entity_typename(tp: Option<&Type>) -> Result<&EntityTypeName> {
    match tp.ok_or(QueryExprError::TypeAnnotationNone)? {
        Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => entity_lub_to_typename(&lub),
        _ => Err(QueryExprError::TypecheckError),
    }
}


/// This is a Cedar expression intended to be more easily converted into a SQL query.
/// It refines the Cedar expression language by specifying the types of
/// `GetAttr` and `HasAttr`. Here, `U` is the type of unknowns
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum QueryExpr<U = UnknownType> {
    Lit(Literal),
    // Skipped: Var, Slot; these should be removed by partial evaluation/policy instantiation
    Unknown { name: U, type_annotation: cedar_policy_core::ast::Type },  // type annotation is mandatory
    If { test_expr: Box<QueryExpr<U>>, then_expr: Box<QueryExpr<U>>, else_expr: Box<QueryExpr<U>> },
    And { left: Box<QueryExpr<U>>, right: Box<QueryExpr<U>> },
    Or { left: Box<QueryExpr<U>>, right: Box<QueryExpr<U>> },
    UnaryApp { op: UnaryOp, arg: Box<QueryExpr<U>> },
    BinaryApp { op: BinaryOp, left: Box<QueryExpr<U>>, right: Box<QueryExpr<U>> }, // op should not be `in`
    InEntity {
        left: Box<QueryExpr<U>>,
        right: Box<QueryExpr<U>>,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    },
    InSet {
        left: Box<QueryExpr<U>>,
        right: Box<QueryExpr<U>>,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    },
    MulByConst { arg: Box<QueryExpr<U>>, constant: i64 },
    // TODO: extension functions
    GetAttrEntity {
        expr: Box<QueryExpr<U>>,
        expr_type: EntityTypeName,
        attr: SmolStr
    },
    GetAttrRecord {
        expr: Box<QueryExpr<U>>,
        attr: SmolStr,
        result_type: CastableType  // we need to know the result type because sometimes
                                   // the result will be "json" by default and we need to cast it
    },
    HasAttrRecord {
        expr: Box<QueryExpr<U>>,
        attr: SmolStr,
    },
    IsNotNull(Box<QueryExpr<U>>), // we use this instead of `HasAttr` on entities
    Like { expr: Box<QueryExpr<U>>, pattern: Pattern },
    Set(Vec<QueryExpr<U>>),
    Record { pairs: Vec<(SmolStr, QueryExpr<U>)> }
}

impl<U> Default for QueryExpr<U> {
    fn default() -> Self {
        QueryExpr::Lit(false.into())
    }
}

impl<T: Clone> QueryExpr<T> {
    pub fn contains_or_in_set(left: QueryExpr<T>, right: QueryExpr<T>, left_type: EntityTypeName, right_type: EntityTypeName) -> Self {
        let contains_expr = if left_type == right_type {
            Some(QueryExpr::BinaryApp {
                op: BinaryOp::Contains,
                left: Box::new(right.clone()),
                right: Box::new(left.clone())
            })
        } else { None };
        let inset_expr = QueryExpr::InSet {
            left: Box::new(left),
            right: Box::new(right),
            left_type,
            right_type,
        };
        match contains_expr {
            Some(contains_expr) => QueryExpr::Or {
                left: Box::new(contains_expr),
                right: Box::new(inset_expr)
            },
            None => inset_expr
        }
    }
}

impl TryFrom<&Expr<Option<Type>>> for QueryExpr<SmolStr> {
    type Error = QueryExprError;

    fn try_from(value: &Expr<Option<Type>>) -> Result<Self> {
        match value.expr_kind() {
            ExprKind::Lit(l) => Ok(QueryExpr::Lit(l.to_owned())),
            ExprKind::Var(v) => Err(QueryExprError::VariableAppears(v.to_owned())),
            ExprKind::Slot(s) => Err(QueryExprError::SlotAppears(s.to_owned())),
            ExprKind::Unknown { name, type_annotation } => Ok(QueryExpr::Unknown {
                name: name.to_owned(),
                type_annotation: type_annotation.to_owned().ok_or_else(|| QueryExprError::UnknownNotAnnotated(name.to_owned()))?
            }),
            ExprKind::If { test_expr, then_expr, else_expr } => Ok(QueryExpr::If {
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

                    match arg2.data().as_ref().ok_or(QueryExprError::TypeAnnotationNone)? {
                        Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => Ok(QueryExpr::InEntity {
                            left: Box::new(QueryExpr::try_from(arg1.as_ref())?),
                            right: Box::new(QueryExpr::try_from(arg2.as_ref())?),
                            left_type: arg1_tp_entity.to_owned(),
                            right_type: entity_lub_to_typename(lub)?.to_owned(),
                        }),
                        Type::Set { element_type } => Ok(QueryExpr::contains_or_in_set(
                            QueryExpr::try_from(arg1.as_ref())?,
                            QueryExpr::try_from(arg2.as_ref())?,
                            arg1_tp_entity.to_owned(),
                            type_to_entity_typename(element_type.as_deref())?.to_owned(),
                        )),
                        _ => Err(QueryExprError::TypecheckError)
                    }
                } else {
                    Ok(QueryExpr::BinaryApp {
                        op: *op,
                        left: Box::new(QueryExpr::try_from(arg1.as_ref())?),
                        right: Box::new(QueryExpr::try_from(arg2.as_ref())?),
                    })
                }
            },
            ExprKind::MulByConst { arg, constant } => Ok(QueryExpr::MulByConst {
                arg: Box::new(QueryExpr::try_from(arg.as_ref())?),
                constant: *constant,
            }),
            ExprKind::ExtensionFunctionApp { fn_name, .. } => Err(QueryExprError::ExtensionFunctionAppears(fn_name.to_owned())),
            ExprKind::GetAttr { expr, attr } => {
                let expr_tp = expr.data().as_ref().ok_or(QueryExprError::TypeAnnotationNone)?;
                match expr_tp {
                    Type::EntityOrRecord(EntityRecordKind::Record { .. }) => {
                        Ok(QueryExpr::GetAttrRecord {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            attr: attr.to_owned(),
                            result_type: value.data().as_ref().ok_or(QueryExprError::TypeAnnotationNone)?.try_into()?
                        })
                    },
                    Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => {
                        Ok(QueryExpr::GetAttrEntity {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            expr_type: entity_lub_to_typename(lub)?.to_owned(),
                            attr: attr.to_owned(),
                        })
                    },
                    _ => Err(QueryExprError::TypecheckError),
                }
            },
            ExprKind::HasAttr { expr, attr } => {
                let expr_tp = expr.data().as_ref().ok_or(QueryExprError::TypeAnnotationNone)?;
                match expr_tp {
                    Type::EntityOrRecord(EntityRecordKind::Record { .. }) => {
                        Ok(QueryExpr::HasAttrRecord {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            attr: attr.to_owned(),
                        })
                    },
                    Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => {
                        Ok(QueryExpr::IsNotNull(Box::new(QueryExpr::GetAttrEntity {
                            expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                            expr_type: entity_lub_to_typename(lub)?.to_owned(),
                            attr: attr.to_owned(),
                        })))
                    },
                    _ => Err(QueryExprError::TypecheckError),
                }
            },
            ExprKind::Like { expr, pattern } => {
                Ok(QueryExpr::Like {
                    expr: Box::new(QueryExpr::try_from(expr.as_ref())?),
                    pattern: pattern.to_owned(),
                })
            },
            ExprKind::Set(s) => {
                Ok(QueryExpr::Set(s.iter().map(|e| QueryExpr::try_from(e)).collect::<Result<Vec<_>>>()?))
            },
            ExprKind::Record { pairs } =>  Ok(QueryExpr::Record {
                pairs: pairs.iter().map(|(k, v)| Ok((k.to_owned(), QueryExpr::try_from(v)?))).collect::<Result<Vec<_>>>()?
            })
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OtherUnknown {
    pub(crate) pfx: Option<SmolStr>,
    pub(crate) name: SmolStr
}

/// The default unknown type for a query expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnknownType {
    /// This is the type of unknown that refers to a dereferenced entity
    /// That is, it is on the LHS of a `let` binding or it is supplied as a dereferenced entity
    EntityDeref(SmolStr),
    /// This is the type of unknown that refers to some other value (essentially an escape hatch)
    Other(OtherUnknown),
}

impl<U> QueryExpr<U> {
    // Functorality for `QueryExpr`. Can this be derived automatically?
    pub fn map_unknowns<V>(self, f: &impl Fn(U) -> V) -> QueryExpr<V> {
        match self {
            QueryExpr::Lit(l) => QueryExpr::Lit(l),
            QueryExpr::Unknown { name, type_annotation } => QueryExpr::Unknown {
                name: f(name),
                type_annotation: type_annotation
            },
            QueryExpr::If { test_expr, then_expr, else_expr } => QueryExpr::If {
                test_expr: Box::new(test_expr.map_unknowns(f)),
                then_expr: Box::new(then_expr.map_unknowns(f)),
                else_expr: Box::new(else_expr.map_unknowns(f)),
            },
            QueryExpr::And { left, right } => QueryExpr::And {
                left: Box::new(left.map_unknowns(f)),
                right: Box::new(right.map_unknowns(f)),
            },
            QueryExpr::Or { left, right } => QueryExpr::Or {
                left: Box::new(left.map_unknowns(f)),
                right: Box::new(right.map_unknowns(f)),
            },
            QueryExpr::UnaryApp { op, arg } => QueryExpr::UnaryApp {
                op,
                arg: Box::new(arg.map_unknowns(f)),
            },
            QueryExpr::BinaryApp { op, left, right } => QueryExpr::BinaryApp {
                op,
                left: Box::new(left.map_unknowns(f)),
                right: Box::new(right.map_unknowns(f)),
            },
            QueryExpr::MulByConst { arg, constant } => QueryExpr::MulByConst {
                arg: Box::new(arg.map_unknowns(f)),
                constant,
            },
            QueryExpr::GetAttrRecord { expr, attr, result_type } => QueryExpr::GetAttrRecord {
                expr: Box::new(expr.map_unknowns(f)),
                attr,
                result_type,
            },
            QueryExpr::GetAttrEntity { expr, expr_type, attr } => QueryExpr::GetAttrEntity {
                expr: Box::new(expr.map_unknowns(f)),
                expr_type,
                attr,
            },
            QueryExpr::HasAttrRecord { expr, attr } => QueryExpr::HasAttrRecord {
                expr: Box::new(expr.map_unknowns(f)),
                attr,
            },
            QueryExpr::InEntity { left, right, left_type, right_type } => QueryExpr::InEntity {
                left: Box::new(left.map_unknowns(f)),
                right: Box::new(right.map_unknowns(f)),
                left_type,
                right_type,
            },
            QueryExpr::InSet { left, right, left_type, right_type } => QueryExpr::InSet {
                left: Box::new(left.map_unknowns(f)),
                right: Box::new(right.map_unknowns(f)),
                left_type,
                right_type,
            },
            QueryExpr::IsNotNull(e) => QueryExpr::IsNotNull(Box::new(e.map_unknowns(f))),
            QueryExpr::Like { expr, pattern } => QueryExpr::Like {
                expr: Box::new(expr.map_unknowns(f)),
                pattern,
            },
            QueryExpr::Set(values) => QueryExpr::Set(values.into_iter().map(|e| e.map_unknowns(f)).collect()),
            QueryExpr::Record { pairs } => QueryExpr::Record {
                pairs: pairs.into_iter().map(|(k, v)| (k, v.map_unknowns(f))).collect(),
            },
        }
    }
}

impl From<QueryExpr<SmolStr>> for QueryExpr {
    fn from(qe: QueryExpr<SmolStr>) -> Self {
        qe.map_unknowns(&|s| UnknownType::EntityDeref(s))
    }
}

#[derive(Debug, Clone)]
pub struct BindingValue {
    insertion_order: usize,
    pub(crate) name: SmolStr,
    pub(crate) ty: EntityTypeName
}

impl From<BindingValue> for QueryExpr {
    fn from(bv: BindingValue) -> Self {
        QueryExpr::Unknown {
            name: UnknownType::EntityDeref(bv.name),
            type_annotation: bv.ty.into()
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Bindings(HashMap<Box<QueryExpr>, BindingValue>);

impl Bindings {
    /// Note that this does a sort on the (a priori unordered) bindings
    /// This is optimized for an insert-many iterate-once (but keep track of insertion order) workload
    pub fn iter(&self) -> impl Iterator<Item = (&BindingValue, &QueryExpr)> {
        let mut result: Vec<_> = self.0.iter().collect();
        result.sort_by(|(_, a), (_, b)| a.insertion_order.cmp(&b.insertion_order));
        result.into_iter().map(|(k, v)| (v, k.as_ref()))
    }

    pub fn insert(&mut self, q: Box<QueryExpr>, ty: EntityTypeName, id_gen: &mut IdGen) -> BindingValue {
        let size = self.0.len();
        self.0.entry(q).or_insert_with(|| {
            BindingValue {
                name: id_gen.next(),
                ty,
                insertion_order: size
            }
        }).clone()
    }
}

/// A sequence of let bindings followed by an expression.
#[derive(Debug, Clone)]
pub struct ExprWithBindings {
    pub(crate) bindings: Bindings,
    pub(crate) expr: Box<QueryExpr>
}

impl From<QueryExpr> for ExprWithBindings {
    fn from(expr: QueryExpr) -> Self {
        ExprWithBindings {
            bindings: Bindings::default(),
            expr: Box::new(expr)
        }
    }
}

// TODO: keep track of existing identifiers so we don't generate duplicates
pub struct IdGen {
    next_id: usize
}

impl IdGen {
    pub fn new() -> Self {
        IdGen { next_id: 0 }
    }

    pub fn next(&mut self) -> SmolStr {
        let id = self.next_id;
        self.next_id += 1;
        SmolStr::new(format!("v__entity_attr_{}", id))
    }
}

impl QueryExpr {
    /// An expression is said to be attr-reduced when the only
    /// expressions that appear on the left argument of a `GetAttrEntity` are of the form `Unknown(EntityDeref(_))`
    /// This function turns the expression into an attr-reduced form.
    pub fn reduce_attrs(&mut self, bindings: &mut Bindings, id_gen: &mut IdGen) {
        match self {
            QueryExpr::Lit(_) => (),
            QueryExpr::Unknown { .. } => (),
            QueryExpr::If { test_expr, then_expr, else_expr } => {
                test_expr.reduce_attrs(bindings, id_gen);
                then_expr.reduce_attrs(bindings, id_gen);
                else_expr.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::And { left, right } => {
                left.reduce_attrs(bindings, id_gen);
                right.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::Or { left, right } => {
                left.reduce_attrs(bindings, id_gen);
                right.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::UnaryApp { arg, .. } => {
                arg.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::BinaryApp { left, right, .. } => {
                left.reduce_attrs(bindings, id_gen);
                right.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::MulByConst { arg, .. } => {
                arg.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::GetAttrRecord { expr, .. } => {
                expr.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::GetAttrEntity { expr, expr_type, .. } => {
                if expr.is_unknown_entity_deref() { return };
                expr.reduce_attrs(bindings, id_gen);

                let expr_owned = std::mem::take(expr);
                let bv = bindings.insert(expr_owned, expr_type.clone(), id_gen);
                *expr = Box::new(bv.into());

                // bindings.push(Binding {
                //     name: new_name,
                //     expr: std::mem::replace(expr, Box::new(new_expr)),
                //     ty: expr_type.clone()
                // });
            },
            QueryExpr::InEntity { left, right, .. } => {
                left.reduce_attrs(bindings, id_gen);
                right.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::InSet { left, right, .. } => {
                left.reduce_attrs(bindings, id_gen);
                right.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::HasAttrRecord { expr, .. } => {
                expr.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::IsNotNull(arg) => {
                arg.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::Like { expr, .. } => {
                expr.reduce_attrs(bindings, id_gen);
            },
            QueryExpr::Set(values) => {
                for v in values {
                    v.reduce_attrs(bindings, id_gen);
                }
            },
            QueryExpr::Record { pairs } => {
                for (_, v) in pairs {
                    v.reduce_attrs(bindings, id_gen);
                }
            },
        }
    }

    /// If this expression is of the form `Unknown(EntityDeref(s))`, return `Some(s)`.
    /// In reduced-attr form, this should succeed on all arguments of GetAttrEntity.
    pub fn get_unknown_entity_deref_name(&self) -> Option<SmolStr> {
        match self {
            QueryExpr::Unknown { name: UnknownType::EntityDeref(s), .. } => Some(s.clone()),
            _ => None
        }
    }

    /// Equivalent to `self.get_unknown_entity_deref_name().is_some()`
    pub fn is_unknown_entity_deref(&self) -> bool {
        matches!(self, QueryExpr::Unknown { name: UnknownType::EntityDeref(_), .. })
    }
}


impl ExprWithBindings {
    /// Turn the expression with bindings into an attr-reduced form.
    pub fn reduce_attrs(&mut self, id_gen: &mut IdGen) {
        self.expr.reduce_attrs(&mut self.bindings, id_gen);
    }
}

// #[test]
// fn test() {
//     let ex: Expr = r#"unknown("foo: "#.parse().unwrap();
// }