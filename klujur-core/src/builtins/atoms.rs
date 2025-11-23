// klujur-core - Atom built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Atom operations: atom, reset!, swap!, compare-and-set!, watches, validators

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Atom Creation and Predicate
// ============================================================================

/// (atom x) - Create an atom with initial value x
pub(crate) fn builtin_atom(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("atom", 1, args.len()));
    }
    Ok(KlujurVal::atom(args[0].clone()))
}

/// (atom? x) - Returns true if x is an atom
pub(crate) fn builtin_atom_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("atom?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Atom(_))))
}

// ============================================================================
// Basic Operations
// ============================================================================

/// (reset! atom newval) - Set atom value, returns newval
/// This is a placeholder - reset! is implemented as a special form in eval.rs
pub(crate) fn builtin_reset(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset!", 2, args.len()));
    }
    // This should never be called - reset! is handled as a special form
    Err(Error::syntax(
        "reset!",
        "reset! must be called directly, not passed as a value",
    ))
}

// Note: swap! and swap-vals! are implemented as special forms in eval/dynamic.rs
// They are not registered as builtins because they need to evaluate the function
// argument before applying it (which builtins cannot do).

/// (reset-vals! atom newval) - Set atom value, returns [old new]
/// This is a placeholder - reset-vals! is implemented as a special form in eval.rs
pub(crate) fn builtin_reset_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset-vals!", 2, args.len()));
    }
    // This should never be called - reset-vals! is handled as a special form
    Err(Error::syntax(
        "reset-vals!",
        "reset-vals! must be called directly, not passed as a value",
    ))
}

/// (compare-and-set! atom oldval newval) - CAS, returns true if successful
pub(crate) fn builtin_compare_and_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("compare-and-set!", 3, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            let success = a.compare_and_set(&args[1], args[2].clone());
            Ok(KlujurVal::bool(success))
        }
        other => Err(Error::type_error_in(
            "compare-and-set!",
            "atom",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Watches
// ============================================================================

/// (add-watch atom key fn) - Add a watch function
pub(crate) fn builtin_add_watch(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("add-watch", 3, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            a.add_watch(args[1].clone(), args[2].clone());
            Ok(args[0].clone())
        }
        other => Err(Error::type_error_in("add-watch", "atom", other.type_name())),
    }
}

/// (remove-watch atom key) - Remove a watch function
pub(crate) fn builtin_remove_watch(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove-watch", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            a.remove_watch(&args[1]);
            Ok(args[0].clone())
        }
        other => Err(Error::type_error_in(
            "remove-watch",
            "atom",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Validators
// ============================================================================

/// (set-validator! atom fn) - Set validation function (nil to remove)
pub(crate) fn builtin_set_validator(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("set-validator!", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            let validator = match &args[1] {
                KlujurVal::Nil => None,
                f => Some(f.clone()),
            };
            a.set_validator(validator);
            Ok(KlujurVal::Nil)
        }
        other => Err(Error::type_error_in(
            "set-validator!",
            "atom",
            other.type_name(),
        )),
    }
}

/// (get-validator atom) - Get validation function or nil
pub(crate) fn builtin_get_validator(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("get-validator", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => Ok(a.get_validator().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "get-validator",
            "atom",
            other.type_name(),
        )),
    }
}
