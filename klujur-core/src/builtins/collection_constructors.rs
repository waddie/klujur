// klujur-core - Collection constructor built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Collection constructors: vec, set, hash-map, hash-set, sorted-map, sorted-set, list*, zipmap

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

use super::to_seq;

use crate::builtins::sequences::builtin_seq;

// ============================================================================
// Collection Constructors
// ============================================================================

/// (vec coll) - convert collection to vector
pub(crate) fn builtin_vec(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vec", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::vector(vec![])),
        KlujurVal::Vector(_, _) => Ok(args[0].clone()),
        _ => {
            let items = to_seq(&args[0])?;
            Ok(KlujurVal::vector(items))
        }
    }
}

/// (set coll) - convert collection to set
pub(crate) fn builtin_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("set", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::set(vec![])),
        KlujurVal::Set(_, _) => Ok(args[0].clone()),
        _ => {
            let items = to_seq(&args[0])?;
            Ok(KlujurVal::set(items))
        }
    }
}

/// (hash-map & kvs) - create hash map from key-value pairs
pub(crate) fn builtin_hash_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "hash-map",
            "requires an even number of arguments",
        ));
    }
    let mut result = klujur_parser::OrdMap::new();
    for pair in args.chunks(2) {
        result.insert(pair[0].clone(), pair[1].clone());
    }
    Ok(KlujurVal::Map(result, None))
}

/// (hash-set & keys) - create hash set from elements
pub(crate) fn builtin_hash_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::set(args.to_vec()))
}

/// (sorted-map & kvs) - create sorted map (our default map is already sorted)
pub(crate) fn builtin_sorted_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    // Our OrdMap is already sorted
    builtin_hash_map(args)
}

/// (sorted-set & keys) - create sorted set (our default set is already sorted)
pub(crate) fn builtin_sorted_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    // Our OrdSet is already sorted
    builtin_hash_set(args)
}

/// (list* args) or (list* a args) or (list* a b args) - create list with last arg spread
pub(crate) fn builtin_list_star(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // (list* coll) => seq of coll
        return builtin_seq(args);
    }

    // Collect all but last arg, then spread the last
    let mut result: Vec<KlujurVal> = args[..args.len() - 1].to_vec();
    let last = &args[args.len() - 1];
    let spread = to_seq(last)?;
    result.extend(spread);

    Ok(KlujurVal::list(result))
}

/// (zipmap keys vals) - create map from parallel key/value seqs
pub(crate) fn builtin_zipmap(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("zipmap", 2, args.len()));
    }
    let keys = to_seq(&args[0])?;
    let vals = to_seq(&args[1])?;

    let mut result = klujur_parser::OrdMap::new();
    for (k, v) in keys.into_iter().zip(vals) {
        result.insert(k, v);
    }
    Ok(KlujurVal::Map(result, None))
}
