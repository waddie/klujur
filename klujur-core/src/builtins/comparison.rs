// klujur-core - Comparison built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Comparison operations: =, not=, <, >, <=, >=, ==, compare, identical?

use klujur_parser::{KlujurLazySeq, KlujurVal, SeqResult};

use crate::error::Result;

use super::{compare_numbers, force_lazy_seq};

// ============================================================================
// Equality
// ============================================================================

/// Realize a lazy sequence into a list for comparison.
/// Recursively walks the lazy seq, forcing each element.
fn realize_to_list(ls: &KlujurLazySeq) -> Result<KlujurVal> {
    let mut elements = Vec::new();
    let mut current = KlujurVal::LazySeq(ls.clone());

    loop {
        match current {
            KlujurVal::Nil => break,
            KlujurVal::List(ref items, _) if items.is_empty() => break,
            KlujurVal::List(ref items, _) => {
                elements.extend(items.iter().cloned());
                break;
            }
            KlujurVal::LazySeq(ref ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => break,
                SeqResult::Cons(first, rest) => {
                    elements.push(first);
                    current = rest;
                }
            },
            other => {
                // Unexpected type in rest position
                elements.push(other);
                break;
            }
        }
    }

    Ok(KlujurVal::list(elements))
}

/// Prepare a value for equality comparison by realizing lazy sequences.
fn prepare_for_eq(val: &KlujurVal) -> Result<KlujurVal> {
    match val {
        KlujurVal::LazySeq(ls) => realize_to_list(ls),
        _ => Ok(val.clone()),
    }
}

pub(crate) fn builtin_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }

    // Realize any lazy sequences before comparing
    let prepared: Result<Vec<KlujurVal>> = args.iter().map(prepare_for_eq).collect();
    let prepared = prepared?;

    for i in 1..prepared.len() {
        if prepared[i - 1] != prepared[i] {
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

    // Realize any lazy sequences before comparing
    let prepared: Result<Vec<KlujurVal>> = args.iter().map(prepare_for_eq).collect();
    let prepared = prepared?;

    for i in 1..prepared.len() {
        if prepared[i - 1] == prepared[i] {
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
