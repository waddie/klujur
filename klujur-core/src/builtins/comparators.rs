// klujur-core - Comparator utilities for sorted collections
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Comparator utilities for sorted-map-by and sorted-set-by.
//!
//! Provides functions to call user-defined comparators and perform
//! binary search on sorted collections.

use std::cmp::Ordering;

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};
use crate::eval::apply::apply;

/// Call a comparator function and return Ordering.
///
/// Handles both:
/// - 3-way comparators (returns int: negative, zero, or positive)
/// - Boolean comparators (returns true if a < b)
///
/// For boolean comparators, two calls may be needed to distinguish
/// "equal" from "greater than".
pub fn call_comparator(comp: &KlujurVal, a: &KlujurVal, b: &KlujurVal) -> Result<Ordering> {
    let result = apply(comp, &[a.clone(), b.clone()])?;

    match result {
        KlujurVal::Int(n) => {
            if n < 0 {
                Ok(Ordering::Less)
            } else if n > 0 {
                Ok(Ordering::Greater)
            } else {
                Ok(Ordering::Equal)
            }
        }
        KlujurVal::Bool(true) => {
            // a < b
            Ok(Ordering::Less)
        }
        KlujurVal::Bool(false) => {
            // Either a >= b. Need to call again to distinguish = from >
            let reverse = apply(comp, &[b.clone(), a.clone()])?;
            match reverse {
                KlujurVal::Bool(true) => {
                    // b < a, so a > b
                    Ok(Ordering::Greater)
                }
                _ => {
                    // Neither a < b nor b < a, so a = b
                    Ok(Ordering::Equal)
                }
            }
        }
        _ => Err(Error::EvalError(format!(
            "Comparator must return int or boolean, got: {}",
            result.type_name()
        ))),
    }
}

/// Binary search for a key in a sorted map's entries using a custom comparator.
///
/// Returns Ok(index) if found, Err(index) if not found where index is the
/// insertion point.
pub fn binary_search_map(
    entries: &[(KlujurVal, KlujurVal)],
    key: &KlujurVal,
    comp: &KlujurVal,
) -> Result<std::result::Result<usize, usize>> {
    if entries.is_empty() {
        return Ok(Err(0));
    }

    let mut low: usize = 0;
    let mut high: usize = entries.len();

    while low < high {
        let mid = low + (high - low) / 2;
        let cmp = call_comparator(comp, key, &entries[mid].0)?;

        match cmp {
            Ordering::Less => {
                high = mid;
            }
            Ordering::Greater => {
                low = mid + 1;
            }
            Ordering::Equal => {
                return Ok(Ok(mid));
            }
        }
    }

    Ok(Err(low))
}

/// Binary search for an element in a sorted set using a custom comparator.
///
/// Returns Ok(index) if found, Err(index) if not found where index is the
/// insertion point.
pub fn binary_search_set(
    elements: &[KlujurVal],
    elem: &KlujurVal,
    comp: &KlujurVal,
) -> Result<std::result::Result<usize, usize>> {
    if elements.is_empty() {
        return Ok(Err(0));
    }

    let mut low: usize = 0;
    let mut high: usize = elements.len();

    while low < high {
        let mid = low + (high - low) / 2;
        let cmp = call_comparator(comp, elem, &elements[mid])?;

        match cmp {
            Ordering::Less => {
                high = mid;
            }
            Ordering::Greater => {
                low = mid + 1;
            }
            Ordering::Equal => {
                return Ok(Ok(mid));
            }
        }
    }

    Ok(Err(low))
}
