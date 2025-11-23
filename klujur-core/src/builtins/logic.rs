// klujur-core - Logic built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Logic operations: not, boolean

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Logic
// ============================================================================

/// (not x) - logical negation
pub(crate) fn builtin_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("not", 1, args.len()));
    }
    Ok(KlujurVal::bool(!args[0].is_truthy()))
}

/// (boolean x) - coerce to boolean
pub(crate) fn builtin_boolean(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("boolean", 1, args.len()));
    }
    Ok(KlujurVal::bool(args[0].is_truthy()))
}
