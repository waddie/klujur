// klujur-core - Comparison built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Comparison operations: =, not=, <, >, <=, >=, ==, compare, identical?

use klujur_parser::KlujurVal;

use crate::error::Result;

use super::compare_numbers;

// ============================================================================
// Equality
// ============================================================================

pub(crate) fn builtin_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if args[i - 1] != args[i] {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

pub(crate) fn builtin_not_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    // (not=) and (not= x) return true per Clojure semantics
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if args[i - 1] == args[i] {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

// ============================================================================
// Ordering
// ============================================================================

pub(crate) fn builtin_lt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? != std::cmp::Ordering::Less {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

pub(crate) fn builtin_gt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? != std::cmp::Ordering::Greater {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

pub(crate) fn builtin_le(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? == std::cmp::Ordering::Greater {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

pub(crate) fn builtin_ge(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? == std::cmp::Ordering::Less {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}
