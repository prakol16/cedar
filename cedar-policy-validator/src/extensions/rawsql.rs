use cedar_policy_core::extensions::rawsql;

use crate::extension_schema::ExtensionSchema;

/// Construct the extension schema
pub fn extension_schema() -> ExtensionSchema {
    ExtensionSchema::from_extn(rawsql::extension(), true)
}
