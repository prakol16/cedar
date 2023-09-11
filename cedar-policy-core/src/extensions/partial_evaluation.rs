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

//! This module contains the extension for including unknown values
use crate::{
    ast::{CallStyle, EntityType, Extension, ExtensionFunction, ExtensionOutputValue, Value, Name},
    entities::SchemaType,
    evaluator::{self, EvaluationError},
};

use self::names::{EXTENSION_NAME, UNKNOWN_FUN_NAME, ERROR_FUN_NAME};

// PANIC SAFETY All the names are valid names
#[allow(clippy::expect_used)]
mod names {
    use crate::ast::{Name, Id};

    lazy_static::lazy_static! {
        pub static ref EXTENSION_NAME : Name = Name::parse_unqualified_name("partial_evaluation").expect("should be a valid identifier");

        pub static ref UNKNOWN_FUN_NAME: Name = Name::parse_unqualified_name("unknown").expect("should be a valid identifier");
        pub static ref ERROR_FUN_NAME: Name = Name::parse_unqualified_name("error").expect("should be a valid identifier");

        pub static ref BOOL_TYPE_ID : Id = "bool".parse().expect("bool is a valid identifier");
        pub static ref LONG_TYPE_ID : Id = "long".parse().expect("long is a valid identifier");
        pub static ref STR_TYPE_ID : Id = "str".parse().expect("str is a valid identifier");
        pub static ref ENTITY_TYPE_ID : Id = "entity".parse().expect("entity is a valid identifier");
    }
}

fn create_new_unknown(v: Value) -> evaluator::Result<ExtensionOutputValue> {
    Ok(ExtensionOutputValue::Unknown(v.get_as_string()?.to_owned(), None))
    // let s = v.get_as_string()?.to_string();
    // Dirty hack to identify types
    // match s.split_once(": ") {
    //     Some((s1, s2)) => Ok(ExtensionOutputValue::Unknown(
    //         s1.into(),
    //         Some(SchemaType::Entity {
    //             ty: EntityType::Concrete(s2.parse().map_err(|_| {
    //                 EvaluationError::failed_extension_function_application(
    //                     EXTENSION_NAME.clone(),
    //                     format!("Failed to parse entity type name {}", s2),
    //                 )
    //             })?),
    //         }),
    //     )),
    //     None => Ok(ExtensionOutputValue::Unknown(s.into(), None)),
    // }
}

fn create_new_unknown_typed(v: Value, ty: SchemaType) -> evaluator::Result<ExtensionOutputValue> {
    Ok(ExtensionOutputValue::Unknown(
        v.get_as_string()?.to_owned(),
        Some(ty),
    ))
}

fn create_new_unknown_entity(v: Value, ty: Value) -> evaluator::Result<ExtensionOutputValue> {
    let ty = ty.get_as_string()?;
    let ty = EntityType::Concrete(ty.parse().map_err(|e| {
        EvaluationError::failed_extension_function_application(
            EXTENSION_NAME.clone(),
            format!("Failed to parse entity type name {} due to {}", ty, e),
        )
    })?);
    create_new_unknown_typed(v, SchemaType::Entity { ty })
}

fn throw_error(v: Value) -> evaluator::Result<ExtensionOutputValue> {
    let msg = v.get_as_string()?;
    let err = EvaluationError::failed_extension_function_application(
        EXTENSION_NAME.clone(),
        msg.to_string(),
    );
    Err(err)
}

/// Construct the extension
pub fn extension() -> Extension {
    Extension::new(
        "partial_evaluation".parse().unwrap(),
        [
            ExtensionFunction::unary_never(
                UNKNOWN_FUN_NAME.clone(),
                CallStyle::FunctionStyle,
                Box::new(create_new_unknown),
                Some(SchemaType::String),
            ),
            ExtensionFunction::binary_never(
                Name::type_in_namespace(names::ENTITY_TYPE_ID.clone(), names::UNKNOWN_FUN_NAME.clone()),
                CallStyle::FunctionStyle,
                Box::new(create_new_unknown_entity),
                (Some(SchemaType::String), Some(SchemaType::String)),
            ),
            ExtensionFunction::unary_never(
                ERROR_FUN_NAME.clone(),
                CallStyle::FunctionStyle,
                Box::new(throw_error),
                Some(SchemaType::String),
            ),
        ].into_iter().chain(
            [
                (names::BOOL_TYPE_ID.clone(), SchemaType::Bool),
                (names::LONG_TYPE_ID.clone(), SchemaType::Long),
                (names::STR_TYPE_ID.clone(), SchemaType::String),
            ].into_iter().map(|(tp, schtp)| {
                let schtp_clone = schtp.clone();
                ExtensionFunction::unary(
                    Name::type_in_namespace(tp, names::UNKNOWN_FUN_NAME.clone()),
                    CallStyle::FunctionStyle,
                    Box::new(move |v| {
                        create_new_unknown_typed(v, schtp.clone())
                    }),
                    schtp_clone,
                    Some(SchemaType::String),
                )
            })
        ),
    )
}
