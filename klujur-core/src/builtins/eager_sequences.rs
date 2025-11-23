// klujur-core - Eager sequence built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Eager sequence functions: sort, sort-by, frequencies, group-by, ffirst, nfirst, nnext, fnext, rseq

use klujur_parser::KlujurVal;

use crate::error::{AritySpec, Error, Result};
use crate::eval::apply;

use super::to_seq;

use crate::builtins::additional_predicates::builtin_compare;
use crate::builtins::sequences::{builtin_first, builtin_next};

// ============================================================================
// Eager Sequence Functions
// ============================================================================

/// (sort coll) or (sort comp coll) - sort collection
pub(crate) fn builtin_sort(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            let mut items = to_seq(&args[0])?;
            items.sort_by(|a, b| {
                // Use compare for sorting
                match builtin_compare(&[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    _ => std::cmp::Ordering::Equal,
                }
            });
            Ok(KlujurVal::list(items))
        }
        2 => {
            let comp = &args[0];
            let mut items = to_seq(&args[1])?;
            // Use comparator function
            items.sort_by(|a, b| match apply(comp, &[a.clone(), b.clone()]) {
                Ok(KlujurVal::Int(n)) => {
                    if n < 0 {
                        std::cmp::Ordering::Less
                    } else if n > 0 {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                }
                Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Less,
                Ok(KlujurVal::Bool(false)) => {
                    // For boolean comparators: false could mean a >= b
                    // Check (comp b a) to distinguish Greater from Equal
                    match apply(comp, &[b.clone(), a.clone()]) {
                        Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Greater,
                        _ => std::cmp::Ordering::Equal,
                    }
                }
                _ => std::cmp::Ordering::Equal,
            });
            Ok(KlujurVal::list(items))
        }
        _ => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("sort".into()),
        }),
    }
}

/// (sort-by keyfn coll) or (sort-by keyfn comp coll) - sort by key function
pub(crate) fn builtin_sort_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            let keyfn = &args[0];
            let items = to_seq(&args[1])?;
            // Pre-compute keys
            let mut keyed: Vec<(KlujurVal, KlujurVal)> = items
                .into_iter()
                .map(|item| {
                    let key = apply(keyfn, std::slice::from_ref(&item)).unwrap_or(KlujurVal::Nil);
                    (key, item)
                })
                .collect();
            keyed.sort_by(
                |(a, _), (b, _)| match builtin_compare(&[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    _ => std::cmp::Ordering::Equal,
                },
            );
            let items: Vec<_> = keyed.into_iter().map(|(_, v)| v).collect();
            Ok(KlujurVal::list(items))
        }
        3 => {
            let keyfn = &args[0];
            let comp = &args[1];
            let items = to_seq(&args[2])?;
            // Pre-compute keys
            let mut keyed: Vec<(KlujurVal, KlujurVal)> = items
                .into_iter()
                .map(|item| {
                    let key = apply(keyfn, std::slice::from_ref(&item)).unwrap_or(KlujurVal::Nil);
                    (key, item)
                })
                .collect();
            keyed.sort_by(
                |(a, _), (b, _)| match apply(comp, &[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Less,
                    Ok(KlujurVal::Bool(false)) => {
                        // For boolean comparators: false could mean a >= b
                        // Check (comp b a) to distinguish Greater from Equal
                        match apply(comp, &[b.clone(), a.clone()]) {
                            Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Greater,
                            _ => std::cmp::Ordering::Equal,
                        }
                    }
                    _ => std::cmp::Ordering::Equal,
                },
            );
            let items: Vec<_> = keyed.into_iter().map(|(_, v)| v).collect();
            Ok(KlujurVal::list(items))
        }
        _ => Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("sort-by".into()),
        }),
    }
}

/// (frequencies coll) - map of element->count
pub(crate) fn builtin_frequencies(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("frequencies", 1, args.len()));
    }
    let items = to_seq(&args[0])?;
    let mut counts: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for item in items {
        let count = counts
            .get(&item)
            .and_then(|v| {
                if let KlujurVal::Int(n) = v {
                    Some(*n)
                } else {
                    None
                }
            })
            .unwrap_or(0);
        counts.insert(item, KlujurVal::int(count + 1));
    }
    Ok(KlujurVal::Map(counts, None))
}

/// (group-by f coll) - map of (f elem)->elements
pub(crate) fn builtin_group_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("group-by", 2, args.len()));
    }
    let f = &args[0];
    let items = to_seq(&args[1])?;

    let mut groups: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for item in items {
        let key = apply(f, std::slice::from_ref(&item))?;
        let existing = groups
            .get(&key)
            .cloned()
            .unwrap_or_else(|| KlujurVal::vector(vec![]));
        let new_vec = match existing {
            KlujurVal::Vector(mut v, _) => {
                v.push_back(item);
                KlujurVal::Vector(v, None)
            }
            _ => KlujurVal::vector(vec![item]),
        };
        groups.insert(key, new_vec);
    }
    Ok(KlujurVal::Map(groups, None))
}

/// (ffirst x) - (first (first x))
pub(crate) fn builtin_ffirst(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ffirst", 1, args.len()));
    }
    let first = builtin_first(args)?;
    builtin_first(&[first])
}

/// (nfirst x) - (next (first x))
pub(crate) fn builtin_nfirst(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nfirst", 1, args.len()));
    }
    let first = builtin_first(args)?;
    builtin_next(&[first])
}

/// (nnext x) - (next (next x))
pub(crate) fn builtin_nnext(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nnext", 1, args.len()));
    }
    let next1 = builtin_next(args)?;
    builtin_next(&[next1])
}

/// (fnext x) - (first (next x))
pub(crate) fn builtin_fnext(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("fnext", 1, args.len()));
    }
    let next1 = builtin_next(args)?;
    builtin_first(&[next1])
}

/// (rseq coll) - reverse seq (O(1) for vectors)
pub(crate) fn builtin_rseq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rseq", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                Ok(KlujurVal::list(items.iter().rev().cloned().collect()))
            }
        }
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        other => Err(Error::type_error_in(
            "rseq",
            "reversible collection",
            other.type_name(),
        )),
    }
}
