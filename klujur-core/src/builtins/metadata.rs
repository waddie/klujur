// klujur-core - Metadata built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Metadata operations: meta, with-meta, vary-meta, alter-meta!, reset-meta!

use std::rc::Rc;

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Metadata Access
// ============================================================================

/// (meta obj) - Returns the metadata of obj, or nil if there is none.
pub(crate) fn builtin_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("meta", 1, args.len()));
    }
    match &args[0] {
        // For values with inline metadata
        KlujurVal::Symbol(_, meta)
        | KlujurVal::List(_, meta)
        | KlujurVal::Vector(_, meta)
        | KlujurVal::Map(_, meta)
        | KlujurVal::Set(_, meta) => match meta {
            Some(m) => Ok(KlujurVal::Map((**m).clone(), None)),
            None => Ok(KlujurVal::Nil),
        },
        // For vars, get var metadata
        KlujurVal::Var(v) => match v.meta() {
            Some(m) => Ok(KlujurVal::Map(m, None)),
            None => Ok(KlujurVal::Nil),
        },
        // Other types don't support metadata
        _ => Ok(KlujurVal::Nil),
    }
}

/// (with-meta obj m) - Returns obj with metadata m.
pub(crate) fn builtin_with_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("with-meta", 2, args.len()));
    }
    let meta_map = match &args[1] {
        KlujurVal::Map(m, _) => Some(Rc::new(m.clone())),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::type_error_in(
                "with-meta",
                "map or nil",
                other.type_name(),
            ));
        }
    };
    match args[0].with_meta(meta_map) {
        Some(val) => Ok(val),
        None => Err(Error::EvalError(format!(
            "with-meta: {} doesn't support metadata",
            args[0].type_name()
        ))),
    }
}

// Note: vary-meta is implemented in stdlib (core.cljc) because it operates
// on immutable values. alter-meta! is a special form (in eval/dynamic.rs)
// so it can call user functions while also being usable as a higher-order function.

// ============================================================================
// Metadata Mutation (for references)
// ============================================================================

/// (reset-meta! ref m) - Sets ref's metadata to m.
pub(crate) fn builtin_reset_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset-meta!", 2, args.len()));
    }
    let meta_map = match &args[1] {
        KlujurVal::Map(m, _) => Some(m.clone()),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::type_error_in(
                "reset-meta!",
                "map or nil",
                other.type_name(),
            ));
        }
    };
    match &args[0] {
        KlujurVal::Var(v) => {
            v.set_meta(meta_map.clone());
            // Return the new metadata (or nil)
            match meta_map {
                Some(m) => Ok(KlujurVal::Map(m, None)),
                None => Ok(KlujurVal::Nil),
            }
        }
        KlujurVal::Atom(_) => {
            // Atoms could also support metadata in Clojure
            Err(Error::EvalError(
                "reset-meta!: atoms don't yet support metadata".into(),
            ))
        }
        other => Err(Error::type_error_in(
            "reset-meta!",
            "var or atom",
            other.type_name(),
        )),
    }
}
