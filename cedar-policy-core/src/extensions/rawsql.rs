//! This module contains the rawsql extension, which allows embedding
//! raw SQL in a policy. This SQL is not evaluated by Cedar, but is
//! converted to SQL using the partial evaluation to SQL translation.

use crate::{
    ast::{Extension, ExtensionFunction, ExtensionOutputValue, Name, Value},
    entities::SchemaType,
    evaluator::EvaluationError,
};

use self::names::{BOOL_SQL_ID, LONG_SQL_ID, RAWSQL_ID, RAWSQL_NAME, STR_SQL_ID};

// PANIC SAFETY all of the names here are valid names
#[allow(clippy::expect_used)]
mod names {
    use crate::ast::{Id, Name};

    lazy_static::lazy_static! {
        pub static ref RAWSQL_ID : Id = "rawsql".parse().expect("rawsql is a valid identifier");
        pub static ref RAWSQL_NAME : Name = Name::new(RAWSQL_ID.clone(), []);

        pub static ref BOOL_SQL_ID : Id = "bool".parse().expect("bool is a valid identifier");
        pub static ref LONG_SQL_ID : Id = "long".parse().expect("long is a valid identifier");
        pub static ref STR_SQL_ID : Id = "str".parse().expect("str is a valid identifier");
    }
}

fn get_first_arg(args: &[Value]) -> Result<ExtensionOutputValue, EvaluationError> {
    args.get(0).map_or_else(
        || Err(EvaluationError::failed_extension_function_application(
        RAWSQL_NAME.clone(),
        "The first argument of `rawsql` must be a dummy unknown with name __RAWSQL or a fallback Cedar expression".to_string(),
        )),
        |v| Ok(ExtensionOutputValue::Concrete(v.to_owned()))
    )
}

/// Construct the extension
pub fn extension() -> Extension {
    Extension::new(
        RAWSQL_NAME.clone(),
        [
            (BOOL_SQL_ID.clone(), SchemaType::Bool),
            (LONG_SQL_ID.clone(), SchemaType::Long),
            (STR_SQL_ID.clone(), SchemaType::String),
        ]
        .into_iter()
        .map(|(tp, schtp)| {
            ExtensionFunction::new(
                Name::new(tp, [RAWSQL_ID.clone()]),
                crate::ast::CallStyle::FunctionStyle,
                Box::new(get_first_arg),
                Some(schtp.clone()),
                vec![Some(schtp), Some(SchemaType::String)],
            )
        }),
    )
}
