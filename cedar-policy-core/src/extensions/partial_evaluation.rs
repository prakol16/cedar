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
    ast::{CallStyle, Extension, ExtensionFunction, ExtensionOutputValue, Value, EntityType},
    entities::SchemaType,
    evaluator::{self, EvaluationError},
};

fn create_new_unknown(v: Value) -> evaluator::Result<ExtensionOutputValue> {
    let s = v.get_as_string()?.to_string();
    // Dirty hack to identify types
    match s.split_once(": ") {
        Some((s1, s2)) => Ok(ExtensionOutputValue::Unknown(s1.into(), Some(SchemaType::Entity { ty: EntityType::Concrete(s2.parse().unwrap()) }))),
        None => Ok(ExtensionOutputValue::Unknown(s.into(), None))
    }
}

fn throw_error(v: Value) -> evaluator::Result<ExtensionOutputValue> {
    let msg = v.get_as_string()?;
    // PANIC SAFETY: This name is fully static, and is a valid extension name
    #[allow(clippy::unwrap_used)]
    let err = EvaluationError::failed_extension_function_application(
        "partial_evaluation".parse().unwrap(),
        msg.to_string(),
    );
    Err(err)
}

/// Construct the extension
// PANIC SAFETY: all uses of `unwrap` here on parsing extension names are correct names
#[allow(clippy::unwrap_used)]
pub fn extension() -> Extension {
    Extension::new(
        "partial_evaluation".parse().unwrap(),
        vec![
            ExtensionFunction::unary_never(
                "unknown".parse().unwrap(),
                CallStyle::FunctionStyle,
                Box::new(create_new_unknown),
                Some(SchemaType::String),
            ),
            ExtensionFunction::unary_never(
                "error".parse().unwrap(),
                CallStyle::FunctionStyle,
                Box::new(throw_error),
                Some(SchemaType::String),
            )
        ],
    )
}
