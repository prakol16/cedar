/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

use crate::{ast::{EntityType, Name, Type, Value, Literal}, extensions::Extensions};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::BTreeMap;

/// Possible types that schema-based parsing can expect for Cedar values.
/// This is also the type used to annotate unknowns
/// TODO: move this to `ast`
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SchemaType {
    /// Boolean
    Bool,
    /// Signed integer
    Long,
    /// String
    String,
    /// Set, with homogeneous elements of the specified type
    Set {
        /// Element type
        element_ty: Box<SchemaType>,
    },
    /// Type of the empty set.  (Compatible with all `Set` types)
    EmptySet,
    /// Record, with the specified attributes having the specified types
    Record {
        /// Attributes and their types
        attrs: BTreeMap<SmolStr, AttributeType>,
    },
    /// Entity
    Entity {
        /// Entity type
        ty: EntityType,
    },
    /// Extension types
    Extension {
        /// Name of the extension type.
        ///
        /// Cedar has nominal typing, so two values have the same type iff
        /// they have the same typename here.
        name: Name,
    },
}

/// Attribute type structure used in [`SchemaType`]
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct AttributeType {
    /// Type of the attribute
    attr_type: SchemaType,
    /// Is the attribute required
    required: bool,
}

impl SchemaType {
    /// Does this SchemaType match the given Type.
    /// I.e., are they compatible, in the sense that there exist some concrete
    /// values that have the given SchemaType and the given Type.
    pub fn matches(&self, ty: &Type) -> bool {
        match (self, ty) {
            (SchemaType::Bool, Type::Bool) => true,
            (SchemaType::Long, Type::Long) => true,
            (SchemaType::String, Type::String) => true,
            (SchemaType::Set { .. }, Type::Set) => true,
            (SchemaType::EmptySet, Type::Set) => true,
            (SchemaType::Record { .. }, Type::Record) => true,
            (SchemaType::Entity { ty: ty1 }, Type::Entity { ty: ty2 }) => ty1 == ty2,
            (SchemaType::Extension { name: name1 }, Type::Extension { name: name2 }) => {
                name1 == name2
            }
            _ => false,
        }
    }

    /// Does this SchemaType match the given SchemaType.
    /// I.e., are they compatible, in the sense that there exist some concrete
    /// values that have both types.
    pub fn is_consistent_with(&self, other: &SchemaType) -> bool {
        if self == other {
            true
        } else {
            use SchemaType::*;
            match (self, other) {
                (Set { .. }, EmptySet) => true,
                (EmptySet, Set { .. }) => true,
                (Set { element_ty: elty1 }, Set { element_ty: elty2 }) => {
                    elty1.is_consistent_with(elty2)
                }
                (Record { attrs: attrs1 }, Record { attrs: attrs2 }) => {
                    attrs1.iter().all(|(k, v)| {
                        match attrs2.get(k) {
                            Some(ty) => {
                                // both have the attribute, doesn't matter if
                                // one or both consider it required or optional
                                ty.attr_type.is_consistent_with(&v.attr_type)
                            }
                            None => {
                                // attrs1 has the attribute, attrs2 does not.
                                // if required in attrs1, incompatible.
                                // otherwise fine
                                !v.required
                            }
                        }
                    }) && attrs2.iter().all(|(k, v)| {
                        match attrs1.get(k) {
                            Some(ty) => {
                                // both have the attribute, doesn't matter if
                                // one or both consider it required or optional
                                ty.attr_type.is_consistent_with(&v.attr_type)
                            }
                            None => {
                                // attrs2 has the attribute, attrs1 does not.
                                // if required in attrs2, incompatible.
                                // otherwise fine
                                !v.required
                            }
                        }
                    })
                }
                _ => false,
            }
        }
    }

    /// Get the SchemaType of a given Cedar value
    /// This has a lot of duplicate logic from type_of_rexpr
    /// Returns none if there is a heterogenous set
    /// or if there is an extension function that is missing/without a return type
    pub fn from_value(value: &Value, extensions: &Extensions<'_>) -> Option<Self> {
        match value {
            Value::Lit(l) => Some(match l {
                Literal::Bool(_) => Self::Bool,
                Literal::Long(_) => Self::Long,
                Literal::String(_) => Self::String,
                Literal::EntityUID(u) => Self::Entity {
                    ty: u.entity_type().clone(),
                },
            }),
            Value::Set(elements) => {
                let mut element_types = elements.iter().map(|e| Self::from_value(e, extensions));
                match element_types.next() {
                    Some(Some(element_ty)) => {
                        let all_consistent = element_types.all(|ty| {
                            ty.is_some_and(|ty| element_ty.is_consistent_with(&ty))
                        });
                        if all_consistent {
                            Some(Self::Set {
                                element_ty: Box::new(element_ty),
                            })
                        } else {
                            None
                        }
                    },
                    Some(None) => None,
                    None => Some(Self::EmptySet),
                }
            },
            Value::Record(pairs) => {
                Some(Self::Record {
                    attrs: pairs.iter().map(|(k, v)| {
                        let attr_type = Self::from_value(v, extensions)?;
                        Some((k.clone(), AttributeType::optional(attr_type)))
                    }).collect::<Option<BTreeMap<_,_>>>()?
                })
            },
            Value::ExtensionValue(ext_fn) => {
                let efunc = extensions.func(&ext_fn.typename()).ok()?;
                let return_type = efunc.return_type()?.clone();
                Some(return_type)
            },
        }
    }
}

impl AttributeType {
    /// Constuct a new required attribute type
    pub fn required(attr_type: SchemaType) -> Self {
        Self {
            attr_type,
            required: true,
        }
    }

    /// Construct a new optional attribute type
    pub fn optional(attr_type: SchemaType) -> Self {
        Self {
            attr_type,
            required: false,
        }
    }

    /// Is the attribute required
    pub fn is_required(&self) -> bool {
        self.required
    }

    /// Get the `SchemaType` of the attribute
    pub fn schema_type(&self) -> &SchemaType {
        &self.attr_type
    }

    /// Get the `SchemaType` of the attribute, and whether it is required
    pub fn into_data(self) -> (SchemaType, bool) {
        (self.attr_type, self.required)
    }
}

impl std::fmt::Display for SchemaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Long => write!(f, "long"),
            Self::String => write!(f, "string"),
            Self::Set { element_ty } => write!(f, "(set of {})", &element_ty),
            Self::EmptySet => write!(f, "empty-set"),
            Self::Record { attrs } => {
                if attrs.is_empty() {
                    write!(f, "empty record")
                } else {
                    write!(f, "record with attributes: (")?;
                    for (k, v) in attrs.iter() {
                        write!(f, "{k:?} => {v}, ")?;
                    }
                    write!(f, ")")?;
                    Ok(())
                }
            }
            Self::Entity { ty } => match ty {
                EntityType::Unspecified => write!(f, "(entity of unspecified type)"),
                EntityType::Concrete(name) => write!(f, "(entity of type {})", name),
            },
            Self::Extension { name } => write!(f, "{}", name),
        }
    }
}

impl std::fmt::Display for AttributeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) {}",
            if self.required {
                "required"
            } else {
                "optional"
            },
            &self.attr_type
        )
    }
}
