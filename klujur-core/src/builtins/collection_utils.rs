// klujur-core - Collection utility built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Collection utility operations: keys, vals, find, contains?, select-keys,
//! merge, merge-with, assoc-in, get-in, update, update-in, zipmap, interleave,
//! interpose, frequencies, group-by, partition-by, split-at, split-with, subvec

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};
use crate::eval::apply;

use super::to_seq;

/// (keys map) - returns sequence of map keys
pub(crate) fn builtin_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("keys", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(KlujurVal::list(map.keys().cloned().collect())),
        KlujurVal::Record(r) => {
            // Return keywords for all fields in the record
            let keys: Vec<KlujurVal> = r
                .values
                .keys()
                .map(|k| KlujurVal::Keyword(k.clone()))
                .collect();
            Ok(KlujurVal::list(keys))
        }
        KlujurVal::SortedMapBy(sm) => {
            let keys: Vec<KlujurVal> = sm.entries().iter().map(|(k, _)| k.clone()).collect();
            Ok(KlujurVal::list(keys))
        }
        other => Err(Error::type_error_in("keys", "map", other.type_name())),
    }
}

/// (vals map) - returns sequence of map values
pub(crate) fn builtin_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vals", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(KlujurVal::list(map.values().cloned().collect())),
        KlujurVal::Record(r) => {
            // Return values for all fields in the record
            let vals: Vec<KlujurVal> = r.values.values().cloned().collect();
            Ok(KlujurVal::list(vals))
        }
        KlujurVal::SortedMapBy(sm) => {
            let vals: Vec<KlujurVal> = sm.entries().iter().map(|(_, v)| v.clone()).collect();
            Ok(KlujurVal::list(vals))
        }
        other => Err(Error::type_error_in("vals", "map", other.type_name())),
    }
}

/// (find map key) - returns map entry [key value] for key, or nil
pub(crate) fn builtin_find(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("find", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(map
            .get(&args[1])
            .map(|v| KlujurVal::vector(vec![args[1].clone(), v.clone()]))
            .unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("find", "map", other.type_name())),
    }
}

/// (contains? coll key) - true if key present (index for vectors)
pub(crate) fn builtin_contains_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("contains?", 2, args.len()));
    }
    let contains = match &args[0] {
        KlujurVal::Nil => false,
        KlujurVal::Map(map, _) => map.contains_key(&args[1]),
        KlujurVal::Set(set, _) => set.contains(&args[1]),
        KlujurVal::Vector(items, _) => {
            // For vectors, contains? checks index not value
            match &args[1] {
                KlujurVal::Int(idx) => *idx >= 0 && (*idx as usize) < items.len(),
                _ => false,
            }
        }
        KlujurVal::SortedMapBy(sm) => {
            use super::collection_constructors::sorted_map_by_get;
            sorted_map_by_get(sm, &args[1])?.is_some()
        }
        KlujurVal::SortedSetBy(ss) => {
            use super::collection_constructors::sorted_set_by_contains;
            sorted_set_by_contains(ss, &args[1])?
        }
        other => {
            return Err(Error::type_error_in(
                "contains?",
                "associative collection",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::bool(contains))
}

/// (select-keys map keyseq) - returns map with only specified keys
pub(crate) fn builtin_select_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("select-keys", 2, args.len()));
    }
    let map = match &args[0] {
        KlujurVal::Nil => return Ok(KlujurVal::map(vec![])),
        KlujurVal::Map(m, _) => m,
        other => {
            return Err(Error::type_error_in(
                "select-keys",
                "map",
                other.type_name(),
            ));
        }
    };
    let keys = to_seq(&args[1])?;
    let mut result = klujur_parser::OrdMap::new();
    for key in keys {
        if let Some(val) = map.get(&key) {
            result.insert(key, val.clone());
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (merge & maps) - merge maps left-to-right
pub(crate) fn builtin_merge(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = klujur_parser::OrdMap::new();
    for arg in args {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    result.insert(k.clone(), v.clone());
                }
            }
            other => return Err(Error::type_error_in("merge", "map", other.type_name())),
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (merge-with f & maps) - merge maps, applying f to duplicate keys
pub(crate) fn builtin_merge_with(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let func = &args[0];
    let mut result: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for arg in &args[1..] {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    if let Some(existing) = result.get(k) {
                        let merged = apply(func, &[existing.clone(), v.clone()])?;
                        result.insert(k.clone(), merged);
                    } else {
                        result.insert(k.clone(), v.clone());
                    }
                }
            }
            other => return Err(Error::type_error_in("merge-with", "map", other.type_name())),
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (get-in m ks) or (get-in m ks not-found) - get nested value via key path
pub(crate) fn builtin_get_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("get-in".into()),
        });
    }
    let not_found = args.get(2).cloned().unwrap_or(KlujurVal::Nil);
    let keys = to_seq(&args[1])?;

    let mut current = args[0].clone();
    for key in keys {
        current = match &current {
            KlujurVal::Map(map, _) => map.get(&key).cloned().unwrap_or_else(|| not_found.clone()),
            KlujurVal::Vector(items, _) => {
                if let KlujurVal::Int(idx) = &key {
                    if *idx >= 0 && (*idx as usize) < items.len() {
                        items[*idx as usize].clone()
                    } else {
                        return Ok(not_found);
                    }
                } else {
                    return Ok(not_found);
                }
            }
            KlujurVal::Nil => return Ok(not_found),
            _ => return Ok(not_found),
        };
    }
    Ok(current)
}

/// (assoc-in m ks v) - associate nested value via key path
pub(crate) fn builtin_assoc_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("assoc-in", 3, args.len()));
    }
    let keys = to_seq(&args[1])?;
    if keys.is_empty() {
        return Ok(args[2].clone());
    }

    fn assoc_in_helper(m: &KlujurVal, keys: &[KlujurVal], v: &KlujurVal) -> Result<KlujurVal> {
        if keys.is_empty() {
            return Ok(v.clone());
        }
        let k = &keys[0];
        if keys.len() == 1 {
            // Base case: assoc the value
            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), v.clone());
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, v.clone());
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("assoc-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => {
                    // Create new map
                    Ok(KlujurVal::map(vec![(k.clone(), v.clone())]))
                }
                other => Err(Error::type_error_in(
                    "assoc-in",
                    "associative",
                    other.type_name(),
                )),
            }
        } else {
            // Recursive case: get nested value and recurse
            let nested = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                other => {
                    return Err(Error::type_error_in(
                        "assoc-in",
                        "associative",
                        other.type_name(),
                    ));
                }
            };
            let new_nested = assoc_in_helper(&nested, &keys[1..], v)?;
            // Now assoc the new nested value
            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_nested);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_nested);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("assoc-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_nested)])),
                other => Err(Error::type_error_in(
                    "assoc-in",
                    "associative",
                    other.type_name(),
                )),
            }
        }
    }

    assoc_in_helper(&args[0], &keys, &args[2])
}

/// (update m k f & args) - update value at key by applying f
pub(crate) fn builtin_update(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 {
        return Err(Error::arity_at_least(3, args.len()));
    }
    let m = &args[0];
    let k = &args[1];
    let f = &args[2];
    let extra_args = &args[3..];

    match m {
        KlujurVal::Map(map, _) => {
            let current = map.get(k).cloned().unwrap_or(KlujurVal::Nil);
            let mut call_args = vec![current];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;
            let mut new_map = map.clone();
            new_map.insert(k.clone(), new_val);
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Vector(items, _) => {
            if let KlujurVal::Int(idx) = k {
                if *idx >= 0 && (*idx as usize) < items.len() {
                    let current = items[*idx as usize].clone();
                    let mut call_args = vec![current];
                    call_args.extend(extra_args.iter().cloned());
                    let new_val = apply(f, &call_args)?;
                    let mut new_vec = items.clone();
                    new_vec.set(*idx as usize, new_val);
                    Ok(KlujurVal::Vector(new_vec, None))
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: *idx,
                        length: items.len(),
                    })
                }
            } else {
                Err(Error::type_error_in("update", "integer", k.type_name()))
            }
        }
        KlujurVal::Nil => {
            // Treat nil as empty map
            let mut call_args = vec![KlujurVal::Nil];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;
            Ok(KlujurVal::map(vec![(k.clone(), new_val)]))
        }
        other => Err(Error::type_error_in(
            "update",
            "associative",
            other.type_name(),
        )),
    }
}

/// (update-in m ks f & args) - update nested value by applying f
pub(crate) fn builtin_update_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 {
        return Err(Error::arity_at_least(3, args.len()));
    }
    let m = &args[0];
    let keys = to_seq(&args[1])?;
    let f = &args[2];
    let extra_args = &args[3..];

    if keys.is_empty() {
        // Apply f directly to m
        let mut call_args = vec![m.clone()];
        call_args.extend(extra_args.iter().cloned());
        return apply(f, &call_args);
    }

    fn update_in_helper(
        m: &KlujurVal,
        keys: &[KlujurVal],
        f: &KlujurVal,
        extra_args: &[KlujurVal],
    ) -> Result<KlujurVal> {
        if keys.is_empty() {
            let mut call_args = vec![m.clone()];
            call_args.extend(extra_args.iter().cloned());
            return apply(f, &call_args);
        }

        let k = &keys[0];
        if keys.len() == 1 {
            // Base case: apply f to the value at key
            builtin_update(&[
                m.clone(),
                k.clone(),
                f.clone(),
                // Pack extra_args into rest
            ])?;
            // Actually need to call with extra args
            let current = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                _ => KlujurVal::Nil,
            };
            let mut call_args = vec![current];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;

            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_val);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_val);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("update-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_val)])),
                other => Err(Error::type_error_in(
                    "update-in",
                    "associative",
                    other.type_name(),
                )),
            }
        } else {
            // Recursive case
            let nested = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                other => {
                    return Err(Error::type_error_in(
                        "update-in",
                        "associative",
                        other.type_name(),
                    ));
                }
            };
            let new_nested = update_in_helper(&nested, &keys[1..], f, extra_args)?;

            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_nested);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_nested);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("update-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_nested)])),
                other => Err(Error::type_error_in(
                    "update-in",
                    "associative",
                    other.type_name(),
                )),
            }
        }
    }

    update_in_helper(m, &keys, f, extra_args)
}

/// (update-keys m f) - apply f to all keys in map
pub(crate) fn builtin_update_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("update-keys", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => {
            let f = &args[1];
            let mut result = klujur_parser::OrdMap::new();
            for (k, v) in map.iter() {
                let new_k = apply(f, std::slice::from_ref(k))?;
                result.insert(new_k, v.clone());
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "update-keys",
            "map",
            other.type_name(),
        )),
    }
}

/// (update-vals m f) - apply f to all values in map
pub(crate) fn builtin_update_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("update-vals", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => {
            let f = &args[1];
            let mut result = klujur_parser::OrdMap::new();
            for (k, v) in map.iter() {
                let new_v = apply(f, std::slice::from_ref(v))?;
                result.insert(k.clone(), new_v);
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "update-vals",
            "map",
            other.type_name(),
        )),
    }
}

/// (peek coll) - get head without removing (last for vector, first for list)
pub(crate) fn builtin_peek(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("peek", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "peek",
            "list or vector",
            other.type_name(),
        )),
    }
}

/// (pop coll) - remove head element (last for vector, first for list)
pub(crate) fn builtin_pop(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("pop", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::List(items, _) => {
            if items.is_empty() {
                Err(Error::EvalError("can't pop empty list".into()))
            } else {
                let mut new_items = items.clone();
                new_items.pop_front();
                Ok(KlujurVal::List(new_items, None))
            }
        }
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Err(Error::EvalError("can't pop empty vector".into()))
            } else {
                let mut new_items = items.clone();
                new_items.pop_back();
                Ok(KlujurVal::Vector(new_items, None))
            }
        }
        other => Err(Error::type_error_in(
            "pop",
            "list or vector",
            other.type_name(),
        )),
    }
}

/// (disj set & keys) - remove keys from set
pub(crate) fn builtin_disj(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Set(set, _) => {
            let mut new_set = set.clone();
            for key in &args[1..] {
                new_set.remove(key);
            }
            Ok(KlujurVal::Set(new_set, None))
        }
        KlujurVal::SortedSetBy(ss) => {
            use super::collection_constructors::sorted_set_by_disj;
            let mut result = ss.clone();
            for key in &args[1..] {
                result = sorted_set_by_disj(&result, key)?;
            }
            Ok(KlujurVal::SortedSetBy(result))
        }
        other => Err(Error::type_error_in("disj", "set", other.type_name())),
    }
}

/// (empty coll) - returns empty collection of same type
pub(crate) fn builtin_empty(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("empty", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(_, _) => Ok(KlujurVal::empty_list()),
        KlujurVal::Vector(_, _) => Ok(KlujurVal::vector(vec![])),
        KlujurVal::Map(_, _) => Ok(KlujurVal::map(vec![])),
        KlujurVal::Set(_, _) => Ok(KlujurVal::set(vec![])),
        KlujurVal::String(_) => Ok(KlujurVal::string("")),
        KlujurVal::SortedMapBy(sm) => Ok(KlujurVal::SortedMapBy(sm.empty())),
        KlujurVal::SortedSetBy(ss) => Ok(KlujurVal::SortedSetBy(ss.empty())),
        other => Err(Error::type_error_in(
            "empty",
            "collection",
            other.type_name(),
        )),
    }
}
