use std::collections::HashMap;

use cedar_policy::EntityTypeName;
use cedar_policy_core::ast::{Expr, Literal, UnaryOp, BinaryOp, Pattern, ExprKind, SlotId, Var, Name, EntityType};
use cedar_policy_validator::types::{Type, Primitive, EntityRecordKind, EntityLUB};
use ref_cast::RefCast;
use smol_str::SmolStr;
use thiserror::Error;

use crate::query_expr_iterator::{QueryExprParentType, QueryExprIterator};


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


#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AttrOrId {
    Attr(SmolStr),
    /// This attribute is the ID of the entity
    Id(SmolStr)
}

/// This is a Cedar expression intended to be more easily converted into a SQL query.
/// It refines the Cedar expression language by specifying the types of
/// `GetAttr` and `HasAttr`. Here, `U` is the type of unknowns
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum QueryExpr {
    Lit(Literal),
    // Skipped: Var, Slot; these should be removed by partial evaluation/policy instantiation
    Unknown { name: UnknownType, type_annotation: Option<EntityTypeName> },  // type annotation is mandatory
    If { test_expr: Box<QueryExpr>, then_expr: Box<QueryExpr>, else_expr: Box<QueryExpr> },
    And { left: Box<QueryExpr>, right: Box<QueryExpr> },
    Or { left: Box<QueryExpr>, right: Box<QueryExpr> },
    UnaryApp { op: UnaryOp, arg: Box<QueryExpr> },
    BinaryApp { op: BinaryOp, left: Box<QueryExpr>, right: Box<QueryExpr> }, // op should not be `in`
    InEntity {
        left: Box<QueryExpr>,
        right: Box<QueryExpr>,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    },
    InSet {
        left: Box<QueryExpr>,
        right: Box<QueryExpr>,
        left_type: EntityTypeName,
        right_type: EntityTypeName,
    },
    MulByConst { arg: Box<QueryExpr>, constant: i64 },
    // TODO: extension functions
    GetAttrEntity {
        expr: Box<QueryExpr>,
        expr_type: EntityTypeName,
        attr: AttrOrId
    },
    GetAttrRecord {
        expr: Box<QueryExpr>,
        attr: SmolStr,
        result_type: CastableType  // we need to know the result type because sometimes
                                   // the result will be "json" by default and we need to cast it
    },
    HasAttrRecord {
        expr: Box<QueryExpr>,
        attr: SmolStr,
    },
    IsNotNull(Box<QueryExpr>), // we use this instead of `HasAttr` on entities
    Like { expr: Box<QueryExpr>, pattern: Pattern },
    Set(Vec<QueryExpr>),
    Record { pairs: Vec<(SmolStr, QueryExpr)> }
}

impl Default for QueryExpr {
    fn default() -> Self {
        QueryExpr::Lit(false.into())
    }
}

impl QueryExpr {
    pub fn eq_or_in_entity(left: QueryExpr, right: QueryExpr, left_type: EntityTypeName, right_type: EntityTypeName) -> Self {
        let eq_expr = if left_type == right_type {
            Some(QueryExpr::BinaryApp {
                op: BinaryOp::Eq,
                left: Box::new(left.clone()),
                right: Box::new(right.clone())
            })
        } else { None };
        let in_entity_expr = QueryExpr::InEntity {
            left: Box::new(left),
            right: Box::new(right),
            left_type,
            right_type,
        };
        match eq_expr {
            Some(eq_expr) => QueryExpr::Or {
                left: Box::new(eq_expr),
                right: Box::new(in_entity_expr)
            },
            None => in_entity_expr
        }
    }

    pub fn contains_or_in_set(left: QueryExpr, right: QueryExpr, left_type: EntityTypeName, right_type: EntityTypeName) -> Self {
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

impl TryFrom<&Expr<Option<Type>>> for QueryExpr {
    type Error = QueryExprError;

    fn try_from(value: &Expr<Option<Type>>) -> Result<Self> {
        match value.expr_kind() {
            ExprKind::Lit(l) => Ok(QueryExpr::Lit(l.to_owned())),
            ExprKind::Var(v) => Err(QueryExprError::VariableAppears(v.to_owned())),
            ExprKind::Slot(s) => Err(QueryExprError::SlotAppears(s.to_owned())),
            ExprKind::Unknown { name, type_annotation } => Ok(QueryExpr::Unknown {
                name: UnknownType { pfx: None, name: name.to_owned() },
                type_annotation: match type_annotation {
                    Some(cedar_policy_core::ast::Type::Entity { ty: EntityType::Concrete(n) }) =>
                        Some(EntityTypeName::ref_cast(n).to_owned()),
                    _ => None,
                }
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
                        Type::EntityOrRecord(EntityRecordKind::Entity(lub)) => Ok(QueryExpr::eq_or_in_entity(
                            QueryExpr::try_from(arg1.as_ref())?,
                            QueryExpr::try_from(arg2.as_ref())?,
                            arg1_tp_entity.to_owned(),
                            entity_lub_to_typename(lub)?.to_owned(),
                        )),
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
                            attr: AttrOrId::Attr(attr.to_owned()),
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
                            attr: AttrOrId::Attr(attr.to_owned()),
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

/// The default unknown type for a query expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnknownType {
    /// Escape hatch for non-entity variables -- for entities, will be ignored
    pub pfx: Option<SmolStr>,
    /// The name (column) of the unknown
    pub name: SmolStr
}

impl QueryExpr {
    pub fn subexpressions_with_parents(&self) -> impl Iterator<Item = (&QueryExpr, Option<QueryExprParentType>)> {
        QueryExprIterator::new(self).into_iter()
    }

    pub fn subexpressions(&self) -> impl Iterator<Item = &QueryExpr> {
        self.subexpressions_with_parents().map(|(e, _)| e)
    }

    /// Retrieve all the unknowns as well as their types.
    pub fn get_unknowns(&self) -> HashMap<UnknownType, Option<EntityTypeName>> {
        self.subexpressions()
            .filter_map(|e| match e {
                QueryExpr::Unknown { name, type_annotation } => Some((name.clone(), type_annotation.clone())),
                _ => None
            })
            .collect()
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
            name: UnknownType { pfx: None, name: bv.name },
            type_annotation: Some(bv.ty)
        }
    }
}

/// Used to construct bindings -- we keep the expressions in a hash map but also remember the insertion order
#[derive(Debug, Clone, Default)]
pub struct BindingsBuilder(HashMap<Box<QueryExpr>, BindingValue>);

#[derive(Debug, Clone, Default)]
pub struct Bindings(Vec<(BindingValue, Box<QueryExpr>)>);

impl Bindings {
    pub fn iter(&self) -> impl Iterator<Item = (&BindingValue, &QueryExpr)> {
        self.0.iter().map(|(bv, qe)| (bv, qe.as_ref()))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&mut BindingValue, &mut QueryExpr)> {
        self.0.iter_mut().map(|(bv, qe)| (bv, qe.as_mut()))
    }
}

impl BindingsBuilder {
    pub fn build(self) -> Bindings {
        let mut result: Vec<_> = self.0.into_iter().map(|(k, v)| (v, k)).collect();
        result.sort_by(|(a, _), (b, _)| a.insertion_order.cmp(&b.insertion_order));
        Bindings(result)
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
    pub(crate) expr: Box<QueryExpr>,
    /// invariant: expr.get_unknowns() U U b in Bindings, b.expr.get_unknowns() - U b in Bindings, b.name = bindings.get_unknowns()
    free_vars: HashMap<UnknownType, Option<EntityTypeName>>,
}

impl From<QueryExpr> for ExprWithBindings {
    fn from(expr: QueryExpr) -> Self {
        ExprWithBindings {
            bindings: Bindings::default(),
            free_vars: expr.get_unknowns(),
            expr: Box::new(expr),
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
    pub fn reduce_attrs(&mut self, id_gen: &mut IdGen) -> Bindings {
        let mut builder = BindingsBuilder::default();
        self.mut_subexpressions(&mut |expr, _| {
            if let QueryExpr::GetAttrEntity { expr, expr_type, .. } = expr {
                if expr.is_unknown_entity_deref() { // if it is already attr-reduced, skip
                    return;
                }

                let expr_owned = std::mem::take(expr);
                let bv = builder.insert(expr_owned, expr_type.clone(), id_gen);
                *expr = Box::new(bv.into());
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
                        attr: AttrOrId::Id("uid".into())  // we use a default id value of "uid"
                    };
                }
            }
        });
    }

    /// If this expression is of the form `Unknown(EntityDeref(s))`, return `Some(s)`.
    /// In reduced-attr form, this should succeed on all arguments of GetAttrEntity.
    pub fn get_unknown_entity_deref_name(&self) -> Option<SmolStr> {
        match self {
            QueryExpr::Unknown { name: UnknownType { name, .. }, .. } => Some(name.clone()),
            _ => None
        }
    }

    pub fn get_unknown_entity_type(&self) -> Option<&EntityTypeName> {
        match self {
            QueryExpr::Unknown { type_annotation, .. } => type_annotation.as_ref(),
            _ => None
        }
    }

    /// Equivalent to `self.get_unknown_entity_deref_name().is_some()`
    pub fn is_unknown_entity_deref(&self) -> bool {
        matches!(self, QueryExpr::Unknown { .. })
    }
}


impl ExprWithBindings {
    /// Turn the expression with bindings into an attr-reduced form.
    pub fn reduce_attrs(&mut self, id_gen: &mut IdGen) {
        self.bindings = self.expr.reduce_attrs(id_gen);
    }

    /// Get all the free variables
    pub fn get_free_vars(&self) -> &HashMap<UnknownType, Option<EntityTypeName>> {
        &self.free_vars
    }
}

// #[test]
// fn test() {
//     let ex: Expr = r#"unknown("foo: "#.parse().unwrap();
// }