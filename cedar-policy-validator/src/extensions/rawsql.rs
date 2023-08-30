use cedar_policy_core::extensions::rawsql;

use crate::{extension_schema::{ExtensionSchema, ExtensionFunctionType}, types::Type};


/// Construct the extension schema
pub fn extension_schema() -> ExtensionSchema {
    let rawsql_ext = rawsql::extension();

    let fun_tys: Vec<ExtensionFunctionType> = rawsql_ext
        .funcs()
        .map(|f| {
            let return_type = f.return_type().map(|ty| {
                ty.clone().into()
            }).unwrap_or(Type::Never);
            ExtensionFunctionType::new(
                f.name().clone(),
                f.arg_types().into_iter().map(|ty| {
                    ty.as_ref().map(|tp| tp.clone().into()).unwrap_or(Type::Never)
                }).collect(),
                return_type,
                None,
            )
        })
        .collect();
    ExtensionSchema::new(rawsql_ext.name().clone(), fun_tys)
}
