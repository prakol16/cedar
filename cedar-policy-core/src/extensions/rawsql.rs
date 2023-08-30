//! This module contains the rawsql extension, which allows embedding
//! raw SQL in a policy. This SQL is not evaluated by Cedar, but is
//! converted to SQL using the partial evaluation to SQL translation.

use crate::{ast::{Value, ExtensionOutputValue, Extension, ExtensionFunction, Name}, evaluator::EvaluationError, entities::SchemaType};

use self::names::{RAWSQL_NAME, RAWSQL_ID, BOOL_SQL_ID, LONG_SQL_ID, STR_SQL_ID};


mod names {
    use crate::ast::{Name, Id};

    // PANIC SAFETY all of the names here are valid names
    lazy_static::lazy_static! {
        pub static ref RAWSQL_ID : Id = "rawsql".parse().unwrap();
        pub static ref RAWSQL_NAME : Name = Name::new(RAWSQL_ID.clone(), []);

        pub static ref BOOL_SQL_ID : Id = "bool".parse().unwrap();
        pub static ref LONG_SQL_ID : Id = "long".parse().unwrap();
        pub static ref STR_SQL_ID : Id = "str".parse().unwrap();
    }
}

fn make_error(_ : &[Value]) -> Result<ExtensionOutputValue, EvaluationError> {
    Err(EvaluationError::failed_extension_function_application(
        RAWSQL_NAME.clone(),
        "The first argument of `rawsql` must be a dummy unknown with name __RAWSQL. rawsql cannot be evaluated directly".to_string(),
    ))
}

/// Construct the extension
pub fn extension() -> Extension {
    Extension::new(
        RAWSQL_NAME.clone(),
        [
            (BOOL_SQL_ID.clone(), SchemaType::Bool),
            (LONG_SQL_ID.clone(), SchemaType::Long),
            (STR_SQL_ID.clone(), SchemaType::String),
        ].into_iter().map(|(tp, schtp)| {
            ExtensionFunction::new(
                Name::new(tp, [RAWSQL_ID.clone()]),
                crate::ast::CallStyle::FunctionStyle,
                Box::new(make_error),
                Some(schtp),
                vec![None, Some(SchemaType::String)]
            )
        })
    )
}
