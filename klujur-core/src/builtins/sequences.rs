// klujur-core - Sequence built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Sequence operations: first, rest, cons, count, nth, take, drop, etc.

use klujur_parser::{KlujurLazySeq, KlujurVal, SeqResult};

use crate::error::{Error, Result};
use crate::eval::{apply, make_native_fn};

use super::collections::builtin_conj;
use super::{force_lazy_seq, to_seq};

// ============================================================================
// Core Sequence Operations
// ============================================================================

pub(crate) fn builtin_first(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("first", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::String(s) => Ok(s
            .chars()
            .next()
            .map(KlujurVal::char)
            .unwrap_or(KlujurVal::Nil)),
        KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
            SeqResult::Empty => Ok(KlujurVal::Nil),
            SeqResult::Cons(first, _) => Ok(first),
        },
        KlujurVal::SortedMapBy(sm) => {
            let entries = sm.entries();
            Ok(entries
                .first()
                .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                .unwrap_or(KlujurVal::Nil))
        }
        KlujurVal::SortedSetBy(ss) => {
            let elements = ss.elements();
            Ok(elements.first().cloned().unwrap_or(KlujurVal::Nil))
        }
        other => Err(Error::type_error_in("first", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_rest(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rest", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
        }
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
        }
        KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
            SeqResult::Empty => Ok(KlujurVal::empty_list()),
            SeqResult::Cons(_, rest) => Ok(rest),
        },
        KlujurVal::SortedMapBy(sm) => {
            let entries = sm.entries();
            if entries.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                let rest: Vec<KlujurVal> = entries
                    .iter()
                    .skip(1)
                    .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(rest))
            }
        }
        KlujurVal::SortedSetBy(ss) => {
            let elements = ss.elements();
            if elements.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                Ok(KlujurVal::list(elements.iter().skip(1).cloned().collect()))
            }
        }
        other => Err(Error::type_error_in("rest", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_cons(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("cons", 2, args.len()));
    }

    let head = args[0].clone();
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::list(vec![head])),
        KlujurVal::List(items, _) => {
            let mut new_items = items.clone();
            new_items.push_front(head);
            Ok(KlujurVal::List(new_items, None))
        }
        KlujurVal::Vector(items, _) => {
            let mut new_items = items.clone();
            new_items.push_front(head);
            Ok(KlujurVal::List(new_items, None))
        }
        // For lazy seqs, return a Cons with the lazy seq as the rest
        // This preserves laziness - we don't force the lazy seq
        KlujurVal::LazySeq(_) => Ok(KlujurVal::LazySeq(KlujurLazySeq::from_cons(
            head,
            args[1].clone(),
        ))),
        other => Err(Error::type_error_in("cons", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_count(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("count", 1, args.len()));
    }

    let len = match &args[0] {
        KlujurVal::Nil => 0,
        KlujurVal::List(items, _) => items.len(),
        KlujurVal::Vector(items, _) => items.len(),
        KlujurVal::Map(map, _) => map.len(),
        KlujurVal::Set(set, _) => set.len(),
        KlujurVal::String(s) => s.chars().count(),
        KlujurVal::Record(r) => r.values.len(),
        KlujurVal::LazySeq(_) => {
            // Force the lazy-seq and count its elements
            let items = to_seq(&args[0])?;
            items.len()
        }
        KlujurVal::SortedMapBy(sm) => sm.len(),
        KlujurVal::SortedSetBy(ss) => ss.len(),
        other => {
            return Err(Error::type_error_in(
                "count",
                "countable",
                other.type_name(),
            ));
        }
    };

    Ok(KlujurVal::int(len as i64))
}

pub(crate) fn builtin_nth(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("nth".into()),
        });
    }

    let idx = match &args[1] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("nth", "integer", other.type_name())),
    };

    let not_found = args.get(2);

    match &args[0] {
        KlujurVal::List(items, _) => {
            if idx < 0 || idx as usize >= items.len() {
                if let Some(default) = not_found {
                    Ok(default.clone())
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: items.len(),
                    })
                }
            } else {
                Ok(items[idx as usize].clone())
            }
        }
        KlujurVal::Vector(items, _) => {
            if idx < 0 || idx as usize >= items.len() {
                if let Some(default) = not_found {
                    Ok(default.clone())
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: items.len(),
                    })
                }
            } else {
                Ok(items[idx as usize].clone())
            }
        }
        KlujurVal::String(s) => {
            if idx < 0 {
                if let Some(default) = not_found {
                    return Ok(default.clone());
                } else {
                    return Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: s.chars().count(),
                    });
                }
            }
            match s.chars().nth(idx as usize) {
                Some(c) => Ok(KlujurVal::char(c)),
                None => {
                    if let Some(default) = not_found {
                        Ok(default.clone())
                    } else {
                        Err(Error::IndexOutOfBounds {
                            index: idx,
                            length: s.chars().count(),
                        })
                    }
                }
            }
        }
        KlujurVal::LazySeq(_) => {
            // Walk through lazy seq one element at a time to support infinite seqs
            if idx < 0 {
                if let Some(default) = not_found {
                    return Ok(default.clone());
                } else {
                    return Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: 0,
                    });
                }
            }
            let mut current = args[0].clone();
            for _ in 0..idx {
                match builtin_next(&[current.clone()])? {
                    KlujurVal::Nil => {
                        if let Some(default) = not_found {
                            return Ok(default.clone());
                        } else {
                            return Err(Error::IndexOutOfBounds {
                                index: idx,
                                length: 0, // Unknown length
                            });
                        }
                    }
                    next_val => current = next_val,
                }
            }
            // Get the first element of current position
            builtin_first(&[current])
        }
        other => Err(Error::type_error_in("nth", "indexed", other.type_name())),
    }
}

pub(crate) fn builtin_empty_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("empty?", 1, args.len()));
    }

    let is_empty = match &args[0] {
        KlujurVal::Nil => true,
        KlujurVal::List(items, _) => items.is_empty(),
        KlujurVal::Vector(items, _) => items.is_empty(),
        KlujurVal::Map(map, _) => map.is_empty(),
        KlujurVal::Set(set, _) => set.is_empty(),
        KlujurVal::String(s) => s.is_empty(),
        KlujurVal::SortedMapBy(sm) => sm.is_empty(),
        KlujurVal::SortedSetBy(ss) => ss.is_empty(),
        other => return Err(Error::type_error_in("empty?", "seqable", other.type_name())),
    };

    Ok(KlujurVal::bool(is_empty))
}

pub(crate) fn builtin_next(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("next", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.len() <= 1 => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().skip(1).cloned().collect())),
        KlujurVal::Vector(items, _) if items.len() <= 1 => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().skip(1).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(_, rest) => {
                    // next returns nil if rest is empty, otherwise rest as seq
                    builtin_seq(&[rest])
                }
            }
        }
        KlujurVal::SortedMapBy(sm) => {
            let entries = sm.entries();
            if entries.len() <= 1 {
                Ok(KlujurVal::Nil)
            } else {
                let rest: Vec<KlujurVal> = entries
                    .iter()
                    .skip(1)
                    .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(rest))
            }
        }
        KlujurVal::SortedSetBy(ss) => {
            let elements = ss.elements();
            if elements.len() <= 1 {
                Ok(KlujurVal::Nil)
            } else {
                Ok(KlujurVal::list(elements.iter().skip(1).cloned().collect()))
            }
        }
        other => Err(Error::type_error_in("next", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_second(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("second", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("second", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_last(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("last", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("last", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_butlast(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("butlast", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(
            items.iter().take(items.len() - 1).cloned().collect(),
        )),
        KlujurVal::Vector(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(
            items.iter().take(items.len() - 1).cloned().collect(),
        )),
        other => Err(Error::type_error_in(
            "butlast",
            "seqable",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Subsequences
// ============================================================================

pub(crate) fn builtin_take(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("take", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("take", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            // Take n elements from the lazy seq
            let mut result = Vec::with_capacity(n);
            let mut current = KlujurVal::LazySeq(ls.clone());
            while result.len() < n {
                match &current {
                    KlujurVal::Nil => break,
                    KlujurVal::List(items, _) if items.is_empty() => break,
                    KlujurVal::List(items, _) => {
                        let remaining = n - result.len();
                        result.extend(items.iter().take(remaining).cloned());
                        break;
                    }
                    KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => break,
                        SeqResult::Cons(first, rest) => {
                            result.push(first);
                            current = rest;
                        }
                    },
                    _ => break,
                }
            }
            Ok(KlujurVal::list(result))
        }
        other => Err(Error::type_error_in("take", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_drop(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("drop", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("drop", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            // Drop n elements from the lazy seq, return the rest
            let mut current = KlujurVal::LazySeq(ls.clone());
            let mut dropped = 0;
            while dropped < n {
                match &current {
                    KlujurVal::Nil => return Ok(KlujurVal::empty_list()),
                    KlujurVal::List(items, _) if items.is_empty() => {
                        return Ok(KlujurVal::empty_list());
                    }
                    KlujurVal::List(items, _) => {
                        let remaining = n - dropped;
                        return Ok(KlujurVal::list(
                            items.iter().skip(remaining).cloned().collect(),
                        ));
                    }
                    KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => return Ok(KlujurVal::empty_list()),
                        SeqResult::Cons(_, rest) => {
                            dropped += 1;
                            current = rest;
                        }
                    },
                    _ => return Ok(KlujurVal::empty_list()),
                }
            }
            // Return the remaining sequence
            Ok(current)
        }
        other => Err(Error::type_error_in("drop", "seqable", other.type_name())),
    }
}

pub(crate) fn builtin_concat(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = Vec::new();
    for arg in args {
        if arg.is_nil() {
            continue;
        }
        let items = to_seq(arg)?;
        result.extend(items);
    }
    Ok(KlujurVal::list(result))
}

pub(crate) fn builtin_mapcat(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("mapcat", 2, args.len()));
    }
    let f = &args[0];
    let coll = to_seq(&args[1])?;

    let mut result = Vec::new();
    for item in &coll {
        let mapped = apply(f, std::slice::from_ref(item))?;
        if mapped.is_nil() {
            continue;
        }
        let items = to_seq(&mapped)?;
        result.extend(items);
    }
    Ok(KlujurVal::list(result))
}

pub(crate) fn builtin_partition(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 4 {
        return Err(Error::EvalError(
            "partition requires 2 to 4 arguments".into(),
        ));
    }

    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => {
            return Err(Error::type_error_in(
                "partition",
                "integer",
                other.type_name(),
            ));
        }
    };

    if n == 0 {
        return Err(Error::EvalError("partition size must be positive".into()));
    }

    let (step, coll_idx, pad) = match args.len() {
        2 => (n, 1, None),
        3 => {
            // 3-arity is always (partition n step coll)
            let step = match &args[1] {
                KlujurVal::Int(s) => *s as usize,
                other => {
                    return Err(Error::type_error_in(
                        "partition",
                        "integer",
                        other.type_name(),
                    ));
                }
            };
            (step, 2, None)
        }
        4 => {
            let step = match &args[1] {
                KlujurVal::Int(s) => *s as usize,
                other => {
                    return Err(Error::type_error_in(
                        "partition",
                        "integer",
                        other.type_name(),
                    ));
                }
            };
            let pad = Some(&args[2]);
            (step, 3, pad)
        }
        _ => unreachable!(),
    };

    let coll = to_seq(&args[coll_idx])?;
    let pad_vec = pad.map(to_seq).transpose()?.unwrap_or_default();

    let mut result = Vec::new();
    let mut i = 0;

    while i < coll.len() {
        let end = (i + n).min(coll.len());
        let chunk: Vec<KlujurVal> = coll[i..end].to_vec();

        if chunk.len() == n {
            result.push(KlujurVal::list(chunk));
        } else if pad.is_some() {
            // Pad the chunk
            let mut padded = chunk;
            let needed = n - padded.len();
            let mut pad_iter = pad_vec.iter().cycle();
            for _ in 0..needed {
                if let Some(p) = pad_iter.next() {
                    padded.push(p.clone());
                }
            }
            result.push(KlujurVal::list(padded));
        }
        // If chunk.len() < n and no pad, drop incomplete chunk

        i += step;
    }

    Ok(KlujurVal::list(result))
}

pub(crate) fn builtin_reverse(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("reverse", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().rev().cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::vector(items.iter().rev().cloned().collect())),
        other => Err(Error::type_error_in(
            "reverse",
            "seqable",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Sequence Generators
// ============================================================================

pub(crate) fn builtin_range(args: &[KlujurVal]) -> Result<KlujurVal> {
    let (start, end, step) = match args.len() {
        0 => return Err(Error::syntax("range", "requires at least 1 argument")),
        1 => {
            let end = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (0, end, 1)
        }
        2 => {
            let start = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let end = match &args[1] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (start, end, 1)
        }
        3 => {
            let start = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let end = match &args[1] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let step = match &args[2] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (start, end, step)
        }
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(1, 3),
                got: args.len(),
                name: Some("range".into()),
            });
        }
    };

    if step == 0 {
        return Err(Error::EvalError("range step cannot be zero".into()));
    }

    let mut result = Vec::new();
    let mut i = start;
    if step > 0 {
        while i < end {
            result.push(KlujurVal::int(i));
            i += step;
        }
    } else {
        while i > end {
            result.push(KlujurVal::int(i));
            i += step;
        }
    }
    Ok(KlujurVal::list(result))
}

pub(crate) fn builtin_repeat(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("repeat", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => {
            return Err(Error::EvalError("repeat count must be non-negative".into()));
        }
        other => return Err(Error::type_error_in("repeat", "integer", other.type_name())),
    };
    let val = args[1].clone();
    Ok(KlujurVal::list(vec![val; n]))
}

// ============================================================================
// Into (collection conversion)
// ============================================================================

pub(crate) fn builtin_into(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => builtin_into_2(args),
        3 => builtin_into_3(args),
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("into".into()),
        }),
    }
}

/// (into to from) - 2-arity: add all items from `from` into `to`
fn builtin_into_2(args: &[KlujurVal]) -> Result<KlujurVal> {
    let items: Vec<KlujurVal> = match &args[1] {
        KlujurVal::Nil => Vec::new(),
        KlujurVal::List(items, _) => items.iter().cloned().collect(),
        KlujurVal::Vector(items, _) => items.iter().cloned().collect(),
        other => return Err(Error::type_error_in("into", "seqable", other.type_name())),
    };

    match &args[0] {
        KlujurVal::Vector(existing, _) => {
            let mut result = existing.clone();
            for item in items {
                result.push_back(item);
            }
            Ok(KlujurVal::Vector(result, None))
        }
        KlujurVal::List(existing, _) => {
            // into prepends to list (like repeated conj)
            let mut result = existing.clone();
            for item in items {
                result.push_front(item);
            }
            Ok(KlujurVal::List(result, None))
        }
        KlujurVal::Set(existing, _) => {
            let mut result = existing.clone();
            for item in items {
                result.insert(item);
            }
            Ok(KlujurVal::Set(result, None))
        }
        KlujurVal::Map(existing, _) => {
            // Items should be pairs or vectors of [k v]
            let mut result = existing.clone();
            for item in items {
                match item {
                    KlujurVal::Vector(ref kv, _) if kv.len() == 2 => {
                        result.insert(kv[0].clone(), kv[1].clone());
                    }
                    KlujurVal::List(ref kv, _) if kv.len() == 2 => {
                        result.insert(kv[0].clone(), kv[1].clone());
                    }
                    _ => {
                        return Err(Error::type_error_in(
                            "into",
                            "key-value pair",
                            item.type_name(),
                        ));
                    }
                }
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "into",
            "collection",
            other.type_name(),
        )),
    }
}

/// (into to xform from) - 3-arity: transduce `from` through `xform` into `to`
fn builtin_into_3(args: &[KlujurVal]) -> Result<KlujurVal> {
    let to = &args[0];
    let xform = &args[1];
    let from = &args[2];

    // Get the conj function for the target collection type
    let conj_fn = KlujurVal::NativeFn(make_native_fn("conj", builtin_conj));

    // Apply transducer to conj to get transformed reducing function
    let xf = apply(xform, &[conj_fn])?;

    // Iterate lazily over source collection to support early termination
    // This allows transducers like take-xf to terminate before realizing the entire sequence
    let mut result = to.clone();
    let mut current = builtin_seq(std::slice::from_ref(from))?;

    loop {
        match &current {
            KlujurVal::Nil => break,
            _ => {
                let first = builtin_first(&[current.clone()])?;
                let rest = builtin_rest(&[current.clone()])?;

                result = apply(&xf, &[result, first])?;

                // Check for early termination with Reduced
                if let KlujurVal::Reduced(v) = result {
                    result = (*v).clone();
                    break;
                }

                // Move to rest, calling seq to normalize (nil for empty)
                current = builtin_seq(&[rest])?;
            }
        }
    }

    // Call completion arity: (xf result)
    apply(&xf, &[result])
}

// ============================================================================
// Seq conversion
// ============================================================================

pub(crate) fn builtin_seq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seq", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::List(_, _) => Ok(args[0].clone()),
        KlujurVal::Vector(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::List(items.clone(), None)),
        KlujurVal::String(s) if s.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::String(s) => Ok(KlujurVal::list(s.chars().map(KlujurVal::char).collect())),
        KlujurVal::Set(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Set(items, _) => Ok(KlujurVal::list(items.iter().cloned().collect())),
        KlujurVal::Map(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Map(items, _) => {
            let pairs: Vec<KlujurVal> = items
                .iter()
                .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                .collect();
            Ok(KlujurVal::list(pairs))
        }
        KlujurVal::LazySeq(ls) => {
            // Force the lazy seq and check if empty
            match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(_, _) => Ok(args[0].clone()), // Return the lazy seq itself
            }
        }
        KlujurVal::Record(r) => {
            if r.values.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                // Return seq of [key value] pairs like a map
                let pairs: Vec<KlujurVal> = r
                    .values
                    .iter()
                    .map(|(k, v)| KlujurVal::vector(vec![KlujurVal::Keyword(k.clone()), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(pairs))
            }
        }
        KlujurVal::SortedMapBy(sm) => {
            let entries = sm.entries();
            if entries.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                let pairs: Vec<KlujurVal> = entries
                    .iter()
                    .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(pairs))
            }
        }
        KlujurVal::SortedSetBy(ss) => {
            let elements = ss.elements();
            if elements.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                Ok(KlujurVal::list(elements.clone()))
            }
        }
        other => Err(Error::type_error_in("seq", "seqable", other.type_name())),
    }
}
