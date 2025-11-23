// klujur-core - Collection built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Collection operations: list, vector, get, assoc, dissoc, conj

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Collection Constructors
// ============================================================================

pub(crate) fn builtin_list(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::list(args.to_vec()))
}

pub(crate) fn builtin_vector(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::vector(args.to_vec()))
}

// ============================================================================
// Lookup Operations
// ============================================================================

pub(crate) fn builtin_get(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("get".into()),
        });
    }

    let not_found = args.get(2).cloned().unwrap_or(KlujurVal::Nil);

    match &args[0] {
        KlujurVal::Map(map, _) => Ok(map.get(&args[1]).cloned().unwrap_or(not_found)),
        KlujurVal::Vector(items, _) => {
            if let KlujurVal::Int(idx) = &args[1] {
                if *idx >= 0 && (*idx as usize) < items.len() {
                    Ok(items[*idx as usize].clone())
                } else {
                    Ok(not_found)
                }
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Set(set, _) => {
            if set.contains(&args[1]) {
                Ok(args[1].clone())
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Record(r) => {
            // Get on record requires keyword key
            if let KlujurVal::Keyword(kw) = &args[1] {
                Ok(r.get(kw).cloned().unwrap_or(not_found))
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Nil => Ok(not_found),
        _ => Ok(not_found),
    }
}

// ============================================================================
// Modification Operations
// ============================================================================

pub(crate) fn builtin_assoc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 || !(args.len() - 1).is_multiple_of(2) {
        return Err(Error::syntax("assoc", "requires coll and key-value pairs"));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let mut new_map = map.clone();
            for pair in args[1..].chunks(2) {
                new_map.insert(pair[0].clone(), pair[1].clone());
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Vector(items, _) => {
            let mut new_vec = items.clone();
            for pair in args[1..].chunks(2) {
                if let KlujurVal::Int(idx_i64) = &pair[0] {
                    let idx = *idx_i64 as usize;
                    if idx < new_vec.len() {
                        new_vec.set(idx, pair[1].clone());
                    } else {
                        return Err(Error::IndexOutOfBounds {
                            index: *idx_i64,
                            length: new_vec.len(),
                        });
                    }
                } else {
                    return Err(Error::type_error_in(
                        "assoc",
                        "integer",
                        pair[0].type_name(),
                    ));
                }
            }
            Ok(KlujurVal::Vector(new_vec, None))
        }
        KlujurVal::Record(r) => {
            // assoc on record preserves record type
            let mut new_record = (**r).clone();
            for pair in args[1..].chunks(2) {
                if let KlujurVal::Keyword(kw) = &pair[0] {
                    new_record.values.insert(kw.clone(), pair[1].clone());
                } else {
                    return Err(Error::type_error_in(
                        "assoc",
                        "keyword",
                        pair[0].type_name(),
                    ));
                }
            }
            Ok(KlujurVal::Record(std::rc::Rc::new(new_record)))
        }
        KlujurVal::Nil => {
            let mut new_map = klujur_parser::OrdMap::new();
            for pair in args[1..].chunks(2) {
                new_map.insert(pair[0].clone(), pair[1].clone());
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        other => Err(Error::type_error_in(
            "assoc",
            "associative",
            other.type_name(),
        )),
    }
}

pub(crate) fn builtin_dissoc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let mut new_map = map.clone();
            for key in &args[1..] {
                new_map.remove(key);
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Record(r) => {
            // dissoc on record: if base field removed -> returns Map, else Record
            let mut result = KlujurVal::Record(r.clone());
            for key in &args[1..] {
                if let KlujurVal::Keyword(kw) = key {
                    // RecordInstance::dissoc returns appropriate type
                    if let KlujurVal::Record(curr_r) = &result {
                        result = curr_r.dissoc(kw);
                    } else if let KlujurVal::Map(m, _) = &result {
                        // Already converted to map, continue as map
                        let mut new_map = m.clone();
                        new_map.remove(key);
                        result = KlujurVal::Map(new_map, None);
                    }
                }
            }
            Ok(result)
        }
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        other => Err(Error::type_error_in("dissoc", "map", other.type_name())),
    }
}

pub(crate) fn builtin_conj(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    match &args[0] {
        KlujurVal::List(items, _) => {
            // conj adds to front of list
            let mut result = items.clone();
            for item in args[1..].iter().rev() {
                result.push_front(item.clone());
            }
            Ok(KlujurVal::List(result, None))
        }
        KlujurVal::Vector(items, _) => {
            // conj adds to end of vector
            let mut result = items.clone();
            for item in &args[1..] {
                result.push_back(item.clone());
            }
            Ok(KlujurVal::Vector(result, None))
        }
        KlujurVal::Set(set, _) => {
            let mut new_set = set.clone();
            for item in &args[1..] {
                new_set.insert(item.clone());
            }
            Ok(KlujurVal::Set(new_set, None))
        }
        KlujurVal::Nil => Ok(KlujurVal::list(args[1..].to_vec())),
        other => Err(Error::type_error_in(
            "conj",
            "collection",
            other.type_name(),
        )),
    }
}
