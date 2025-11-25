// klujur-core - Set operation built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Set operations for clojure.set namespace: union, intersection, difference,
//! subset?, superset?

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

/// (union & sets) - returns a set that is the union of the input sets
pub(crate) fn builtin_set_union(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = klujur_parser::OrdSet::new();

    for arg in args {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Set(set, _) => {
                for elem in set.iter() {
                    result.insert(elem.clone());
                }
            }
            other => return Err(Error::type_error_in("union", "set", other.type_name())),
        }
    }

    Ok(KlujurVal::Set(result, None))
}

/// (intersection s1 & sets) - returns a set of elements common to all sets
pub(crate) fn builtin_set_intersection(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    // Start with the first set
    let first_set = match &args[0] {
        KlujurVal::Nil => return Ok(KlujurVal::set(vec![])),
        KlujurVal::Set(set, _) => set.clone(),
        other => {
            return Err(Error::type_error_in(
                "intersection",
                "set",
                other.type_name(),
            ));
        }
    };

    if args.len() == 1 {
        return Ok(KlujurVal::Set(first_set, None));
    }

    // Intersect with each subsequent set
    let mut result = first_set;
    for arg in &args[1..] {
        match arg {
            KlujurVal::Nil => return Ok(KlujurVal::set(vec![])),
            KlujurVal::Set(set, _) => {
                // Keep only elements that are in both sets
                result = result
                    .iter()
                    .filter(|elem| set.contains(elem))
                    .cloned()
                    .collect();
            }
            other => {
                return Err(Error::type_error_in(
                    "intersection",
                    "set",
                    other.type_name(),
                ));
            }
        }
    }

    Ok(KlujurVal::Set(result, None))
}

/// (difference s1 & sets) - returns a set of elements in s1 not in other sets
pub(crate) fn builtin_set_difference(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    // Start with the first set
    let first_set = match &args[0] {
        KlujurVal::Nil => return Ok(KlujurVal::set(vec![])),
        KlujurVal::Set(set, _) => set.clone(),
        other => return Err(Error::type_error_in("difference", "set", other.type_name())),
    };

    if args.len() == 1 {
        return Ok(KlujurVal::Set(first_set, None));
    }

    // Remove elements found in subsequent sets
    let mut result = first_set;
    for arg in &args[1..] {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Set(set, _) => {
                for elem in set.iter() {
                    result.remove(elem);
                }
            }
            other => return Err(Error::type_error_in("difference", "set", other.type_name())),
        }
    }

    Ok(KlujurVal::Set(result, None))
}

/// (subset? s1 s2) - returns true if s1 is a subset of s2
pub(crate) fn builtin_subset_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("subset?", 2, args.len()));
    }

    let (s1, s2) = match (&args[0], &args[1]) {
        (KlujurVal::Set(set1, _), KlujurVal::Set(set2, _)) => (set1, set2),
        (KlujurVal::Set(_, _), other) => {
            return Err(Error::type_error_in("subset?", "set", other.type_name()));
        }
        (other, _) => return Err(Error::type_error_in("subset?", "set", other.type_name())),
    };

    // s1 is a subset of s2 if every element of s1 is in s2
    let is_subset = s1.iter().all(|elem| s2.contains(elem));
    Ok(KlujurVal::bool(is_subset))
}

/// (superset? s1 s2) - returns true if s1 is a superset of s2
pub(crate) fn builtin_superset_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("superset?", 2, args.len()));
    }

    let (s1, s2) = match (&args[0], &args[1]) {
        (KlujurVal::Set(set1, _), KlujurVal::Set(set2, _)) => (set1, set2),
        (KlujurVal::Set(_, _), other) => {
            return Err(Error::type_error_in("superset?", "set", other.type_name()));
        }
        (other, _) => return Err(Error::type_error_in("superset?", "set", other.type_name())),
    };

    // s1 is a superset of s2 if every element of s2 is in s1
    let is_superset = s2.iter().all(|elem| s1.contains(elem));
    Ok(KlujurVal::bool(is_superset))
}
