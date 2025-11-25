// klujur-core - Sequence built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Sequence operations: first, rest, cons, count, nth, take, drop, etc.

use std::rc::Rc;

use klujur_parser::{
    KlujurChunk, KlujurChunkedSeq, KlujurLazySeq, KlujurVal, NativeChunkThunk, SeqResult,
};

use crate::error::{Error, Result};
use crate::eval::{apply, make_native_fn};

use super::chunked::force_chunked_rest;
use super::collections::builtin_conj;
use super::{force_lazy_seq, to_seq};

// ============================================================================
// Seqable Trait
// ============================================================================

/// Trait for types that can be treated as sequences.
///
/// Provides `seq_first`, `seq_rest`, and `seq_next` operations that centralise
/// sequence handling logic across multiple collection types.
pub trait Seqable {
    /// Get the first element. Returns `Ok(KlujurVal::Nil)` if empty.
    fn seq_first(&self) -> Result<KlujurVal>;

    /// Get all elements after the first as a list.
    /// Returns `Ok(KlujurVal::empty_list())` if empty or single element.
    fn seq_rest(&self) -> Result<KlujurVal>;

    /// Like `seq_rest` but returns `Ok(KlujurVal::Nil)` instead of empty list
    /// when there are no remaining elements (i.e., when the collection has
    /// 0 or 1 elements).
    fn seq_next(&self) -> Result<KlujurVal> {
        let rest = self.seq_rest()?;
        match &rest {
            KlujurVal::List(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
            _ => Ok(rest),
        }
    }
}

impl Seqable for KlujurVal {
    fn seq_first(&self) -> Result<KlujurVal> {
        match self {
            KlujurVal::Nil => Ok(KlujurVal::Nil),
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                Ok(items.front().cloned().unwrap_or(KlujurVal::Nil))
            }
            KlujurVal::String(s) => Ok(s
                .chars()
                .next()
                .map(KlujurVal::char)
                .unwrap_or(KlujurVal::Nil)),
            KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(first, _) => Ok(first),
            },
            KlujurVal::ChunkedSeq(cs) => {
                // Get first element from the current chunk
                cs.chunk()
                    .nth(0)
                    .cloned()
                    .ok_or_else(|| Error::EvalError("empty chunked-seq".into()))
            }
            KlujurVal::SortedMapBy(sm) => {
                let entries = sm.entries().map_err(|e| Error::EvalError(e.into()))?;
                Ok(entries
                    .first()
                    .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                    .unwrap_or(KlujurVal::Nil))
            }
            KlujurVal::SortedSetBy(ss) => {
                let elements = ss.elements().map_err(|e| Error::EvalError(e.into()))?;
                Ok(elements.first().cloned().unwrap_or(KlujurVal::Nil))
            }
            other => Err(Error::type_error_in("first", "seqable", other.type_name())),
        }
    }

    fn seq_rest(&self) -> Result<KlujurVal> {
        match self {
            KlujurVal::Nil => Ok(KlujurVal::empty_list()),
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
            KlujurVal::String(s) => Ok(KlujurVal::list(
                s.chars().skip(1).map(KlujurVal::char).collect(),
            )),
            KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::empty_list()),
                SeqResult::Cons(_, rest) => Ok(rest),
            },
            KlujurVal::ChunkedSeq(cs) => {
                // If chunk has more elements, return a ChunkedSeq with offset+1
                if let Some(rest_chunk) = cs.chunk().drop_first() {
                    // Return a new ChunkedSeq with the rest of the current chunk
                    Ok(KlujurVal::ChunkedSeq(KlujurChunkedSeq::with_rest(
                        rest_chunk,
                        force_chunked_rest(cs)?,
                    )))
                } else {
                    // Last element of current chunk - move to next chunk
                    let rest = force_chunked_rest(cs)?;
                    if rest == KlujurVal::Nil {
                        Ok(KlujurVal::empty_list())
                    } else {
                        Ok(rest)
                    }
                }
            }
            KlujurVal::SortedMapBy(sm) => {
                let entries = sm.entries().map_err(|e| Error::EvalError(e.into()))?;
                let rest: Vec<KlujurVal> = entries
                    .iter()
                    .skip(1)
                    .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(rest))
            }
            KlujurVal::SortedSetBy(ss) => {
                let elements = ss.elements().map_err(|e| Error::EvalError(e.into()))?;
                Ok(KlujurVal::list(elements.iter().skip(1).cloned().collect()))
            }
            other => Err(Error::type_error_in("rest", "seqable", other.type_name())),
        }
    }

    /// Override `seq_next` to handle LazySeq properly by normalizing with `builtin_seq`.
    fn seq_next(&self) -> Result<KlujurVal> {
        match self {
            KlujurVal::Nil => Ok(KlujurVal::Nil),
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) if items.len() <= 1 => {
                Ok(KlujurVal::Nil)
            }
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
            KlujurVal::String(s) => {
                let char_count = s.chars().count();
                if char_count <= 1 {
                    Ok(KlujurVal::Nil)
                } else {
                    Ok(KlujurVal::list(
                        s.chars().skip(1).map(KlujurVal::char).collect(),
                    ))
                }
            }
            KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(_, rest) => {
                    // next returns nil if rest is empty, otherwise rest as seq
                    builtin_seq(&[rest])
                }
            },
            KlujurVal::ChunkedSeq(cs) => {
                // Like seq_rest but returns nil instead of empty list
                if let Some(rest_chunk) = cs.chunk().drop_first() {
                    // Return a new ChunkedSeq with the rest of the current chunk
                    Ok(KlujurVal::ChunkedSeq(KlujurChunkedSeq::with_rest(
                        rest_chunk,
                        force_chunked_rest(cs)?,
                    )))
                } else {
                    // Last element of current chunk - move to next chunk
                    Ok(force_chunked_rest(cs)?)
                }
            }
            KlujurVal::SortedMapBy(sm) => {
                let entries = sm.entries().map_err(|e| Error::EvalError(e.into()))?;
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
                let elements = ss.elements().map_err(|e| Error::EvalError(e.into()))?;
                if elements.len() <= 1 {
                    Ok(KlujurVal::Nil)
                } else {
                    Ok(KlujurVal::list(elements.iter().skip(1).cloned().collect()))
                }
            }
            other => Err(Error::type_error_in("next", "seqable", other.type_name())),
        }
    }
}

// ============================================================================
// Core Sequence Operations
// ============================================================================

pub(crate) fn builtin_first(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("first", 1, args.len()));
    }
    args[0].seq_first()
}

pub(crate) fn builtin_rest(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rest", 1, args.len()));
    }
    args[0].seq_rest()
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
        KlujurVal::String(s) => {
            let mut result = vec![head];
            for c in s.chars() {
                result.push(KlujurVal::char(c));
            }
            Ok(KlujurVal::list(result))
        }
        // For lazy seqs, return a Cons with the lazy seq as the rest
        // This preserves laziness - we don't force the lazy seq
        KlujurVal::LazySeq(_) => Ok(KlujurVal::LazySeq(KlujurLazySeq::from_cons(
            head,
            args[1].clone(),
        ))),
        // For chunked seqs, also wrap in a lazy-seq cons to preserve laziness
        KlujurVal::ChunkedSeq(_) => Ok(KlujurVal::LazySeq(KlujurLazySeq::from_cons(
            head,
            args[1].clone(),
        ))),
        other => Err(Error::type_error_in("cons", "seqable", other.type_name())),
    }
}

/// Returns the count of items in a collection.
///
/// # Performance
/// - Collections (List, Vector, Map, Set, Record): O(1)
/// - String: O(n) - must iterate UTF-8 bytes to count Unicode characters
/// - LazySeq: O(n) - forces entire sequence
/// - SortedMapBy, SortedSetBy: O(1)
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
        KlujurVal::LazySeq(_) | KlujurVal::ChunkedSeq(_) => {
            // Force the lazy/chunked seq and count its elements
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
    args[0].seq_next()
}

pub(crate) fn builtin_second(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("second", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::String(s) => Ok(s
            .chars()
            .nth(1)
            .map(KlujurVal::char)
            .unwrap_or(KlujurVal::Nil)),
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
        KlujurVal::String(s) => Ok(s
            .chars()
            .last()
            .map(KlujurVal::char)
            .unwrap_or(KlujurVal::Nil)),
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
        KlujurVal::String(s) if s.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::String(s) => {
            // Return all chars except the last as a list
            let chars: Vec<char> = s.chars().collect();
            Ok(KlujurVal::list(
                chars[..chars.len() - 1]
                    .iter()
                    .map(|c| KlujurVal::char(*c))
                    .collect(),
            ))
        }
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
        KlujurVal::Int(n) if *n < 0 => return Ok(KlujurVal::empty_list()), // negative n → empty
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("take", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::String(s) => Ok(KlujurVal::list(
            s.chars().take(n).map(KlujurVal::char).collect(),
        )),
        KlujurVal::LazySeq(ls) => {
            // Take n elements from the lazy seq
            let mut result = Vec::with_capacity(n);
            let mut current = KlujurVal::LazySeq(ls.clone());
            'outer: while result.len() < n {
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
                    KlujurVal::ChunkedSeq(cs) => {
                        // Rest is a chunked seq - take from it
                        for val in cs.chunk().iter() {
                            if result.len() >= n {
                                break 'outer;
                            }
                            result.push(val.clone());
                        }
                        // Move to next chunk/seq
                        current = force_chunked_rest(cs)?;
                    }
                    _ => break,
                }
            }
            Ok(KlujurVal::list(result))
        }
        KlujurVal::ChunkedSeq(cs) => {
            // Take n elements from the chunked seq
            let mut result = Vec::with_capacity(n);
            let mut current: KlujurVal = KlujurVal::ChunkedSeq(cs.clone());
            'outer: while result.len() < n {
                match &current {
                    KlujurVal::Nil => break,
                    KlujurVal::ChunkedSeq(cs) => {
                        // Take from current chunk
                        for val in cs.chunk().iter() {
                            if result.len() >= n {
                                break 'outer;
                            }
                            result.push(val.clone());
                        }
                        // Move to next chunk (or lazy-seq rest)
                        current = force_chunked_rest(cs)?;
                    }
                    KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => break,
                        SeqResult::Cons(first, rest) => {
                            result.push(first);
                            current = rest;
                        }
                    },
                    KlujurVal::List(items, _) if items.is_empty() => break,
                    KlujurVal::List(items, _) => {
                        let remaining = n - result.len();
                        result.extend(items.iter().take(remaining).cloned());
                        break;
                    }
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
        KlujurVal::Int(n) if *n < 0 => 0usize, // negative n → drop nothing
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("drop", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::String(s) => Ok(KlujurVal::list(
            s.chars().skip(n).map(KlujurVal::char).collect(),
        )),
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
                    KlujurVal::ChunkedSeq(cs) => {
                        // Drop within chunked seq
                        let remaining = n - dropped;
                        return drop_from_chunked_seq(cs, remaining);
                    }
                    _ => return Ok(KlujurVal::empty_list()),
                }
            }
            // Return the remaining sequence
            Ok(current)
        }
        KlujurVal::ChunkedSeq(cs) => drop_from_chunked_seq(cs, n),
        other => Err(Error::type_error_in("drop", "seqable", other.type_name())),
    }
}

/// Drop n elements from a chunked sequence
fn drop_from_chunked_seq(cs: &KlujurChunkedSeq, n: usize) -> Result<KlujurVal> {
    let mut current: KlujurVal = KlujurVal::ChunkedSeq(cs.clone());
    let mut remaining = n;

    loop {
        match &current {
            KlujurVal::Nil => return Ok(KlujurVal::empty_list()),
            KlujurVal::ChunkedSeq(cs) => {
                let chunk_len = cs.chunk().len();
                if remaining < chunk_len {
                    // Drop remaining elements from this chunk
                    let mut new_chunk = cs.chunk().clone();
                    for _ in 0..remaining {
                        new_chunk = new_chunk.drop_first().unwrap_or(new_chunk);
                    }
                    return Ok(KlujurVal::ChunkedSeq(KlujurChunkedSeq::with_rest(
                        new_chunk,
                        force_chunked_rest(cs)?,
                    )));
                } else {
                    // Drop entire chunk and continue
                    remaining -= chunk_len;
                    current = force_chunked_rest(cs)?;
                }
            }
            // Rest is a lazy-seq or other seqable - drop remaining from it
            other => {
                if remaining == 0 {
                    return Ok(other.clone());
                }
                return builtin_drop(&[KlujurVal::int(remaining as i64), other.clone()]);
            }
        }
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
        KlujurVal::String(s) => {
            // Reverse string into a list of characters (like Clojure)
            Ok(KlujurVal::list(
                s.chars().rev().map(KlujurVal::char).collect(),
            ))
        }
        other => Err(Error::type_error_in(
            "reverse",
            "seqable",
            other.type_name(),
        )),
    }
}

// Note: repeat is implemented in stdlib (core.cljc) as a lazy sequence
// to support infinite sequences like (repeat x).

// ============================================================================
// Range (chunked for large ranges, eager list for small)
// ============================================================================

/// Default chunk size for chunked sequences
pub const CHUNK_SIZE: usize = 32;

/// (range end), (range start end), or (range start end step) - return finite range
///
/// For small ranges (≤32 elements), returns an eager list.
/// For large ranges (>32 elements), returns a chunked sequence for efficiency.
/// For infinite range (no args), use the stdlib lazy version.
pub(crate) fn builtin_range(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        0 => {
            // (range) with no args - infinite sequence, use stdlib
            Err(Error::EvalError(
                "range with no args requires stdlib lazy version".into(),
            ))
        }
        1 => {
            // (range end) - 0 to end
            let end = as_i64(&args[0], "range")?;
            make_range(0, end, 1)
        }
        2 => {
            // (range start end)
            let start = as_i64(&args[0], "range")?;
            let end = as_i64(&args[1], "range")?;
            make_range(start, end, 1)
        }
        3 => {
            // (range start end step)
            let start = as_i64(&args[0], "range")?;
            let end = as_i64(&args[1], "range")?;
            let step = as_i64(&args[2], "range")?;
            make_range(start, end, step)
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(0, 3),
            got: args.len(),
            name: Some("range".into()),
        }),
    }
}

/// Create a range, choosing between eager list and chunked sequence
fn make_range(start: i64, end: i64, step: i64) -> Result<KlujurVal> {
    if step == 0 {
        return Ok(KlujurVal::empty_list());
    }

    // Calculate the count of elements
    let count = if step > 0 && end > start {
        ((end - start + step - 1) / step) as usize
    } else if step < 0 && start > end {
        ((start - end + (-step) - 1) / (-step)) as usize
    } else {
        0
    };

    if count == 0 {
        Ok(KlujurVal::empty_list())
    } else if count <= CHUNK_SIZE {
        // Small range: return eager list
        Ok(KlujurVal::list(range_vec(start, end, step)))
    } else {
        // Large range: return chunked sequence
        Ok(make_chunked_range(start, end, step))
    }
}

/// Create a chunked range sequence
fn make_chunked_range(start: i64, end: i64, step: i64) -> KlujurVal {
    // Build the first chunk
    let first_chunk = build_range_chunk(start, end, step);

    if first_chunk.is_empty() {
        return KlujurVal::empty_list();
    }

    // Calculate where the next chunk starts
    let next_start = start + (first_chunk.len() as i64) * step;

    // Create a thunk that generates the rest of the range
    let rest_thunk = make_range_thunk(next_start, end, step);

    KlujurVal::ChunkedSeq(KlujurChunkedSeq::new_native(first_chunk, rest_thunk))
}

/// Build a single chunk of range values
fn build_range_chunk(start: i64, end: i64, step: i64) -> KlujurChunk {
    let mut elements = Vec::with_capacity(CHUNK_SIZE);
    let mut i = start;

    if step > 0 {
        while i < end && elements.len() < CHUNK_SIZE {
            elements.push(KlujurVal::int(i));
            i += step;
        }
    } else {
        while i > end && elements.len() < CHUNK_SIZE {
            elements.push(KlujurVal::int(i));
            i += step;
        }
    }

    KlujurChunk::new(elements)
}

/// Create a native thunk that generates the rest of a range as chunked seq
fn make_range_thunk(start: i64, end: i64, step: i64) -> NativeChunkThunk {
    Rc::new(move || {
        // Check if we've reached the end
        let at_end = if step > 0 { start >= end } else { start <= end };

        if at_end {
            Ok(KlujurVal::Nil)
        } else {
            // Build the next chunk
            let chunk = build_range_chunk(start, end, step);

            if chunk.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                // Calculate next chunk start
                let next_start = start + (chunk.len() as i64) * step;

                // Create the next thunk
                let rest_thunk = make_range_thunk(next_start, end, step);

                Ok(KlujurVal::ChunkedSeq(KlujurChunkedSeq::new_native(
                    chunk, rest_thunk,
                )))
            }
        }
    })
}

/// Helper to extract i64 from a KlujurVal
fn as_i64(val: &KlujurVal, fn_name: &str) -> Result<i64> {
    match val {
        KlujurVal::Int(n) => Ok(*n),
        KlujurVal::Float(f) => Ok(*f as i64),
        other => Err(Error::type_error_in(fn_name, "number", other.type_name())),
    }
}

/// Generate a Vec of integers for the range (used for small ranges)
fn range_vec(start: i64, end: i64, step: i64) -> Vec<KlujurVal> {
    if step == 0 {
        return Vec::new();
    }

    // Estimate capacity
    let cap = if step > 0 && end > start {
        ((end - start) / step) as usize
    } else if step < 0 && start > end {
        ((start - end) / (-step)) as usize
    } else {
        0
    };

    let mut result = Vec::with_capacity(cap);
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
    result
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
        KlujurVal::String(s) => s.chars().map(KlujurVal::char).collect(),
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
    // This allows transducers like (take n) to terminate before realizing the entire sequence
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
        KlujurVal::ChunkedSeq(cs) => {
            // Return the chunked seq if non-empty
            if cs.chunk().is_empty() {
                // Force rest to check if there are more chunks
                let rest = force_chunked_rest(cs)?;
                if rest == KlujurVal::Nil {
                    Ok(KlujurVal::Nil)
                } else {
                    // Rest could be ChunkedSeq, LazySeq, or other seqable
                    builtin_seq(&[rest])
                }
            } else {
                Ok(args[0].clone())
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
            let entries = sm.entries().map_err(|e| Error::EvalError(e.into()))?;
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
            let elements = ss.elements().map_err(|e| Error::EvalError(e.into()))?;
            if elements.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                Ok(KlujurVal::list(elements.clone()))
            }
        }
        other => Err(Error::type_error_in("seq", "seqable", other.type_name())),
    }
}
