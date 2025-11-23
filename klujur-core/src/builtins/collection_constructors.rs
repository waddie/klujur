// klujur-core - Collection constructor built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Collection constructors: vec, set, hash-map, hash-set, sorted-map, sorted-set,
//! sorted-map-by, sorted-set-by, list*, zipmap

use klujur_parser::{KlujurSortedMapBy, KlujurSortedSetBy, KlujurVal};

use crate::error::{Error, Result};

use super::comparators::{binary_search_map, binary_search_set};
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

// ============================================================================
// Custom Comparator Collection Constructors
// ============================================================================

/// (sorted-map-by comparator & keyvals) - create sorted map with custom comparator
///
/// The comparator is a function of two args that returns:
/// - negative number if a < b
/// - zero if a = b
/// - positive number if a > b
///
/// Alternatively, a boolean comparator (like <) returns true if a < b.
///
/// Examples:
///   (sorted-map-by > 1 :a 2 :b 3 :c) => {3 :c, 2 :b, 1 :a}
///   (sorted-map-by compare :a 1 :b 2) => {:a 1, :b 2}
pub(crate) fn builtin_sorted_map_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let comparator = args[0].clone();
    let kvs = &args[1..];

    // Validate we have an even number of key-values
    if !kvs.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "sorted-map-by",
            "requires an even number of key-value arguments after comparator",
        ));
    }

    // Create the sorted map
    let sm = KlujurSortedMapBy::new(comparator);

    // Insert all key-value pairs
    if !kvs.is_empty() {
        let mut entries = Vec::with_capacity(kvs.len() / 2);

        for pair in kvs.chunks(2) {
            let key = pair[0].clone();
            let val = pair[1].clone();

            // Binary search to find insertion point
            let search_result = binary_search_map(&entries, &key, sm.comparator())?;

            match search_result {
                Ok(idx) => {
                    // Key already exists, replace value
                    entries[idx].1 = val;
                }
                Err(idx) => {
                    // Insert at the correct position to maintain sorted order
                    entries.insert(idx, (key, val));
                }
            }
        }

        // Update the entries
        *sm.entries_cell().borrow_mut() = entries;
    }

    Ok(KlujurVal::SortedMapBy(sm))
}

/// (sorted-set-by comparator & keys) - create sorted set with custom comparator
///
/// The comparator is a function of two args that returns:
/// - negative number if a < b
/// - zero if a = b
/// - positive number if a > b
///
/// Alternatively, a boolean comparator (like <) returns true if a < b.
///
/// Examples:
///   (sorted-set-by > 3 1 2) => #{3 2 1}
///   (sorted-set-by compare :a :b :c) => #{:a :b :c}
pub(crate) fn builtin_sorted_set_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let comparator = args[0].clone();
    let elems = &args[1..];

    // Create the sorted set
    let ss = KlujurSortedSetBy::new(comparator);

    // Insert all elements
    if !elems.is_empty() {
        let mut elements = Vec::with_capacity(elems.len());

        for elem in elems {
            // Binary search to find insertion point
            let search_result = binary_search_set(&elements, elem, ss.comparator())?;

            match search_result {
                Ok(_) => {
                    // Element already exists (according to comparator), skip it
                }
                Err(idx) => {
                    // Insert at the correct position to maintain sorted order
                    elements.insert(idx, elem.clone());
                }
            }
        }

        // Update the elements
        *ss.elements_cell().borrow_mut() = elements;
    }

    Ok(KlujurVal::SortedSetBy(ss))
}

/// Helper: Insert a key-value pair into a sorted map, returning a new map.
pub(crate) fn sorted_map_by_assoc(
    sm: &KlujurSortedMapBy,
    key: KlujurVal,
    val: KlujurVal,
) -> Result<KlujurSortedMapBy> {
    let mut entries = sm.entries();
    let search_result = binary_search_map(&entries, &key, sm.comparator())?;

    match search_result {
        Ok(idx) => {
            // Key exists, replace value
            entries[idx].1 = val;
        }
        Err(idx) => {
            // Insert at the correct position
            entries.insert(idx, (key, val));
        }
    }

    Ok(KlujurSortedMapBy::from_entries(
        sm.comparator().clone(),
        entries,
    ))
}

/// Helper: Remove a key from a sorted map, returning a new map.
pub(crate) fn sorted_map_by_dissoc(
    sm: &KlujurSortedMapBy,
    key: &KlujurVal,
) -> Result<KlujurSortedMapBy> {
    let mut entries = sm.entries();
    let search_result = binary_search_map(&entries, key, sm.comparator())?;

    if let Ok(idx) = search_result {
        entries.remove(idx);
    }

    Ok(KlujurSortedMapBy::from_entries(
        sm.comparator().clone(),
        entries,
    ))
}

/// Helper: Get a value from a sorted map.
pub fn sorted_map_by_get(sm: &KlujurSortedMapBy, key: &KlujurVal) -> Result<Option<KlujurVal>> {
    let entries = sm.entries();
    let search_result = binary_search_map(&entries, key, sm.comparator())?;

    match search_result {
        Ok(idx) => Ok(Some(entries[idx].1.clone())),
        Err(_) => Ok(None),
    }
}

/// Helper: Insert an element into a sorted set, returning a new set.
pub(crate) fn sorted_set_by_conj(
    ss: &KlujurSortedSetBy,
    elem: KlujurVal,
) -> Result<KlujurSortedSetBy> {
    let mut elements = ss.elements();
    let search_result = binary_search_set(&elements, &elem, ss.comparator())?;

    match search_result {
        Ok(_) => {
            // Element already exists, return unchanged
        }
        Err(idx) => {
            // Insert at the correct position
            elements.insert(idx, elem);
        }
    }

    Ok(KlujurSortedSetBy::from_elements(
        ss.comparator().clone(),
        elements,
    ))
}

/// Helper: Remove an element from a sorted set, returning a new set.
pub(crate) fn sorted_set_by_disj(
    ss: &KlujurSortedSetBy,
    elem: &KlujurVal,
) -> Result<KlujurSortedSetBy> {
    let mut elements = ss.elements();
    let search_result = binary_search_set(&elements, elem, ss.comparator())?;

    if let Ok(idx) = search_result {
        elements.remove(idx);
    }

    Ok(KlujurSortedSetBy::from_elements(
        ss.comparator().clone(),
        elements,
    ))
}

/// Helper: Check if a sorted set contains an element.
pub fn sorted_set_by_contains(ss: &KlujurSortedSetBy, elem: &KlujurVal) -> Result<bool> {
    let elements = ss.elements();
    let search_result = binary_search_set(&elements, elem, ss.comparator())?;
    Ok(search_result.is_ok())
}
