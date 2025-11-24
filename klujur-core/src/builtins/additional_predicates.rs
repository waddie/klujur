// klujur-core - Additional predicate built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Additional predicates: true?, false?, ==, compare, identical?, not-empty,
//! seqable?, sequential?, sorted?, counted?, reversible?, associative?, indexed?

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Additional Predicates
// ============================================================================

/// (true? x) - exactly true (not just truthy)
pub(crate) fn builtin_true_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("true?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(true))))
}

/// (false? x) - exactly false (not just falsy)
pub(crate) fn builtin_false_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("false?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(false))))
}

/// (== x y & more) - numeric equality (coerces types)
pub(crate) fn builtin_num_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }

    // Convert first arg to f64 for comparison
    let first = match &args[0] {
        KlujurVal::Int(n) => *n as f64,
        KlujurVal::Float(n) => *n,
        other => return Err(Error::type_error_in("==", "number", other.type_name())),
    };

    for arg in &args[1..] {
        let val = match arg {
            KlujurVal::Int(n) => *n as f64,
            KlujurVal::Float(n) => *n,
            other => return Err(Error::type_error_in("==", "number", other.type_name())),
        };
        if first != val {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (compare x y) - returns -1, 0, or 1
pub(crate) fn builtin_compare(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("compare", 2, args.len()));
    }

    let result = compare_values(&args[0], &args[1])?;
    Ok(KlujurVal::int(match result {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }))
}

/// Internal comparison function using iterative approach for vectors
fn compare_values(a: &KlujurVal, b: &KlujurVal) -> Result<std::cmp::Ordering> {
    use std::cmp::Ordering;

    // Work item: (left_val, right_val, pending_length_cmp)
    // pending_length_cmp is used when we finish comparing vector elements
    // and need to fall back to length comparison
    enum WorkItem {
        Compare(KlujurVal, KlujurVal),
        VectorLengthCheck(Ordering),
    }

    let mut work_stack: Vec<WorkItem> = vec![WorkItem::Compare(a.clone(), b.clone())];

    while let Some(item) = work_stack.pop() {
        match item {
            WorkItem::VectorLengthCheck(len_ord) => {
                // All elements were equal, so return the length comparison
                if len_ord != Ordering::Equal {
                    return Ok(len_ord);
                }
                // Otherwise continue checking remaining items
            }
            WorkItem::Compare(a, b) => {
                let ord = match (&a, &b) {
                    // Numbers
                    (KlujurVal::Int(a), KlujurVal::Int(b)) => a.cmp(b),
                    (KlujurVal::Float(a), KlujurVal::Float(b)) => a
                        .partial_cmp(b)
                        .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?,
                    (KlujurVal::Int(a), KlujurVal::Float(b)) => {
                        let fa = *a as f64;
                        fa.partial_cmp(b)
                            .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?
                    }
                    (KlujurVal::Float(a), KlujurVal::Int(b)) => {
                        let fb = *b as f64;
                        a.partial_cmp(&fb)
                            .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?
                    }
                    // Strings
                    (KlujurVal::String(a), KlujurVal::String(b)) => a.cmp(b),
                    // Keywords
                    (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a.cmp(b),
                    // Symbols
                    (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a.cmp(b),
                    // Vectors (lexicographic) - iterative approach
                    (KlujurVal::Vector(a_vec, _), KlujurVal::Vector(b_vec, _)) => {
                        let len_cmp = a_vec.len().cmp(&b_vec.len());
                        let min_len = a_vec.len().min(b_vec.len());

                        // Push length check first (will be processed last)
                        work_stack.push(WorkItem::VectorLengthCheck(len_cmp));

                        // Push element pairs in reverse order for left-to-right processing
                        for i in (0..min_len).rev() {
                            work_stack.push(WorkItem::Compare(a_vec[i].clone(), b_vec[i].clone()));
                        }

                        // Continue to process elements
                        continue;
                    }
                    // Booleans (false < true)
                    (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a.cmp(b),
                    // Nil
                    (KlujurVal::Nil, KlujurVal::Nil) => Ordering::Equal,
                    // Type mismatch
                    (a, b) => {
                        return Err(Error::EvalError(format!(
                            "compare: cannot compare {} and {}",
                            a.type_name(),
                            b.type_name()
                        )));
                    }
                };

                // If we found a non-equal comparison, return immediately
                if ord != Ordering::Equal {
                    return Ok(ord);
                }
                // If equal, continue checking remaining items on stack
            }
        }
    }

    // Stack empty, everything was equal
    Ok(std::cmp::Ordering::Equal)
}

/// (identical? x y) - reference equality
pub(crate) fn builtin_identical_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("identical?", 2, args.len()));
    }

    // For value types, check value equality
    // For reference types, check pointer equality
    let identical = match (&args[0], &args[1]) {
        (KlujurVal::Nil, KlujurVal::Nil) => true,
        (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a == b,
        (KlujurVal::Int(a), KlujurVal::Int(b)) => a == b,
        (KlujurVal::Float(a), KlujurVal::Float(b)) => a.to_bits() == b.to_bits(),
        (KlujurVal::Char(a), KlujurVal::Char(b)) => a == b,
        // For Rc types, we use pointer equality
        (KlujurVal::String(a), KlujurVal::String(b)) => std::ptr::eq(a.as_ref(), b.as_ref()),
        (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a == b, // Interned, pointer eq
        (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a == b,     // Interned, pointer eq
        // Different types are never identical
        _ => false,
    };

    Ok(KlujurVal::bool(identical))
}

/// (not-empty coll) - returns coll if non-empty, else nil
pub(crate) fn builtin_not_empty(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("not-empty", 1, args.len()));
    }

    let is_empty = match &args[0] {
        KlujurVal::Nil => true,
        KlujurVal::List(items, _) => items.is_empty(),
        KlujurVal::Vector(items, _) => items.is_empty(),
        KlujurVal::Map(map, _) => map.is_empty(),
        KlujurVal::Set(set, _) => set.is_empty(),
        KlujurVal::String(s) => s.is_empty(),
        other => {
            return Err(Error::type_error_in(
                "not-empty",
                "seqable",
                other.type_name(),
            ));
        }
    };

    if is_empty {
        Ok(KlujurVal::Nil)
    } else {
        Ok(args[0].clone())
    }
}

/// (seqable? x) - can call seq on x?
pub(crate) fn builtin_seqable_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seqable?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Nil
            | KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::String(_)
            | KlujurVal::SortedMapBy(_)
            | KlujurVal::SortedSetBy(_)
    )))
}

/// (sequential? x) - is x sequential (list/vector)?
pub(crate) fn builtin_sequential_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sequential?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _) | KlujurVal::Vector(_, _)
    )))
}

/// (sorted? x) - is x a sorted collection?
pub(crate) fn builtin_sorted_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sorted?", 1, args.len()));
    }
    // Our OrdMap and OrdSet are sorted by default, as are sorted-map-by and sorted-set-by
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::SortedMapBy(_)
            | KlujurVal::SortedSetBy(_)
    )))
}

/// (counted? x) - is count O(1)?
pub(crate) fn builtin_counted_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("counted?", 1, args.len()));
    }
    // All our collections have O(1) count
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::String(_)
            | KlujurVal::SortedMapBy(_)
            | KlujurVal::SortedSetBy(_)
    )))
}

/// (reversible? x) - can call rseq on x?
pub(crate) fn builtin_reversible_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("reversible?", 1, args.len()));
    }
    // Vectors and sorted collections are reversible
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::SortedMapBy(_)
            | KlujurVal::SortedSetBy(_)
    )))
}

/// (associative? x) - supports assoc? (map/vector)
pub(crate) fn builtin_associative_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("associative?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Map(_, _) | KlujurVal::Vector(_, _) | KlujurVal::SortedMapBy(_)
    )))
}

/// (indexed? x) - supports nth?
pub(crate) fn builtin_indexed_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("indexed?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, _) | KlujurVal::List(_, _) | KlujurVal::String(_)
    )))
}
