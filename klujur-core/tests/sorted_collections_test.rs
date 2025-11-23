// klujur-core - Sorted collections integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for sorted-map-by and sorted-set-by collections.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser};

fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, &env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

fn eval_bool(s: &str) -> bool {
    match eval_str(s) {
        Ok(KlujurVal::Bool(b)) => b,
        _ => panic!("Expected boolean result for: {}", s),
    }
}

fn eval_int(s: &str) -> i64 {
    match eval_str(s) {
        Ok(KlujurVal::Int(n)) => n,
        _ => panic!("Expected integer result for: {}", s),
    }
}

// =============================================================================
// sorted-map-by
// =============================================================================

#[test]
fn test_sorted_map_by_creation() {
    // Empty sorted map
    let result = eval_str("(sorted-map-by <)").unwrap();
    assert!(matches!(result, KlujurVal::SortedMapBy(_)));

    // Sorted map with key-values
    let result = eval_str("(sorted-map-by < 2 :b 1 :a 3 :c)").unwrap();
    assert!(matches!(result, KlujurVal::SortedMapBy(_)));
}

#[test]
fn test_sorted_map_by_ordering() {
    // Ascending order (using <)
    assert_eq!(
        eval_str("(keys (sorted-map-by < 2 :b 1 :a 3 :c))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );

    // Descending order (using >)
    assert_eq!(
        eval_str("(keys (sorted-map-by > 2 :b 1 :a 3 :c))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(2),
            KlujurVal::int(1)
        ])
    );
}

#[test]
fn test_sorted_map_by_get() {
    // Get existing key
    assert_eq!(
        eval_str("(get (sorted-map-by < 1 :a 2 :b) 1)").unwrap(),
        KlujurVal::Keyword(Keyword::new("a"))
    );

    // Get missing key returns nil
    assert_eq!(
        eval_str("(get (sorted-map-by < 1 :a 2 :b) 3)").unwrap(),
        KlujurVal::Nil
    );

    // Get missing key with default
    assert_eq!(
        eval_str("(get (sorted-map-by < 1 :a 2 :b) 3 :not-found)").unwrap(),
        KlujurVal::Keyword(Keyword::new("not-found"))
    );
}

#[test]
fn test_sorted_map_by_assoc() {
    // Add new key
    assert_eq!(
        eval_str("(keys (assoc (sorted-map-by < 1 :a 3 :c) 2 :b))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );

    // Replace existing key
    assert_eq!(
        eval_str("(get (assoc (sorted-map-by < 1 :a) 1 :new) 1)").unwrap(),
        KlujurVal::Keyword(Keyword::new("new"))
    );
}

#[test]
fn test_sorted_map_by_dissoc() {
    assert_eq!(
        eval_str("(keys (dissoc (sorted-map-by < 1 :a 2 :b 3 :c) 2))").unwrap(),
        KlujurVal::list(vec![KlujurVal::int(1), KlujurVal::int(3)])
    );
}

#[test]
fn test_sorted_map_by_count() {
    assert_eq!(eval_int("(count (sorted-map-by <))"), 0);
    assert_eq!(eval_int("(count (sorted-map-by < 1 :a 2 :b))"), 2);
}

#[test]
fn test_sorted_map_by_seq() {
    // seq returns [k v] vectors in sorted order
    assert_eq!(
        eval_str("(first (sorted-map-by < 2 :b 1 :a))").unwrap(),
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::Keyword(Keyword::new("a"))
        ])
    );

    // rest returns remaining entries
    assert_eq!(
        eval_str("(count (rest (sorted-map-by < 1 :a 2 :b 3 :c)))").unwrap(),
        KlujurVal::int(2)
    );
}

#[test]
fn test_sorted_map_by_callable() {
    // Call sorted map as function
    assert_eq!(
        eval_str("((sorted-map-by < 1 :a 2 :b) 1)").unwrap(),
        KlujurVal::Keyword(Keyword::new("a"))
    );

    // With default value
    assert_eq!(
        eval_str("((sorted-map-by < 1 :a 2 :b) 3 :default)").unwrap(),
        KlujurVal::Keyword(Keyword::new("default"))
    );
}

#[test]
fn test_sorted_map_by_predicates() {
    assert!(eval_bool("(sorted? (sorted-map-by < 1 :a))"));
    assert!(eval_bool("(coll? (sorted-map-by < 1 :a))"));
    assert!(eval_bool("(seqable? (sorted-map-by < 1 :a))"));
    assert!(eval_bool("(associative? (sorted-map-by < 1 :a))"));
    assert!(eval_bool("(counted? (sorted-map-by < 1 :a))"));
}

#[test]
fn test_sorted_map_by_conj() {
    // conj with [k v] vector
    assert_eq!(
        eval_str("(keys (conj (sorted-map-by < 1 :a 3 :c) [2 :b]))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// sorted-set-by
// =============================================================================

#[test]
fn test_sorted_set_by_creation() {
    // Empty sorted set
    let result = eval_str("(sorted-set-by <)").unwrap();
    assert!(matches!(result, KlujurVal::SortedSetBy(_)));

    // Sorted set with elements
    let result = eval_str("(sorted-set-by < 2 1 3)").unwrap();
    assert!(matches!(result, KlujurVal::SortedSetBy(_)));
}

#[test]
fn test_sorted_set_by_ordering() {
    // Ascending order
    assert_eq!(
        eval_str("(seq (sorted-set-by < 2 1 3))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );

    // Descending order
    assert_eq!(
        eval_str("(seq (sorted-set-by > 2 1 3))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(2),
            KlujurVal::int(1)
        ])
    );
}

#[test]
fn test_sorted_set_by_conj() {
    assert_eq!(
        eval_str("(seq (conj (sorted-set-by < 1 3) 2))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );

    // conj preserves order when adding to front
    assert_eq!(
        eval_str("(first (conj (sorted-set-by > 2 3) 5))").unwrap(),
        KlujurVal::int(5)
    );
}

#[test]
fn test_sorted_set_by_disj() {
    assert_eq!(
        eval_str("(seq (disj (sorted-set-by < 1 2 3) 2))").unwrap(),
        KlujurVal::list(vec![KlujurVal::int(1), KlujurVal::int(3)])
    );
}

#[test]
fn test_sorted_set_by_contains() {
    assert!(eval_bool("(contains? (sorted-set-by < 1 2 3) 2)"));
    assert!(!eval_bool("(contains? (sorted-set-by < 1 2 3) 4)"));
}

#[test]
fn test_sorted_set_by_get() {
    // get returns the element if present
    assert_eq!(
        eval_str("(get (sorted-set-by < 1 2 3) 2)").unwrap(),
        KlujurVal::int(2)
    );

    // get returns nil if not present
    assert_eq!(
        eval_str("(get (sorted-set-by < 1 2 3) 4)").unwrap(),
        KlujurVal::Nil
    );

    // get with default
    assert_eq!(
        eval_str("(get (sorted-set-by < 1 2 3) 4 :not-found)").unwrap(),
        KlujurVal::Keyword(Keyword::new("not-found"))
    );
}

#[test]
fn test_sorted_set_by_count() {
    assert_eq!(eval_int("(count (sorted-set-by <))"), 0);
    assert_eq!(eval_int("(count (sorted-set-by < 1 2 3))"), 3);
}

#[test]
fn test_sorted_set_by_first_rest() {
    assert_eq!(
        eval_str("(first (sorted-set-by > 1 2 3))").unwrap(),
        KlujurVal::int(3)
    );

    assert_eq!(
        eval_str("(seq (rest (sorted-set-by > 1 2 3)))").unwrap(),
        KlujurVal::list(vec![KlujurVal::int(2), KlujurVal::int(1)])
    );
}

#[test]
fn test_sorted_set_by_callable() {
    // Call sorted set as function (returns element if present)
    assert_eq!(
        eval_str("((sorted-set-by < 1 2 3) 2)").unwrap(),
        KlujurVal::int(2)
    );

    // Returns nil if not present
    assert_eq!(
        eval_str("((sorted-set-by < 1 2 3) 4)").unwrap(),
        KlujurVal::Nil
    );

    // With default value
    assert_eq!(
        eval_str("((sorted-set-by < 1 2 3) 4 :default)").unwrap(),
        KlujurVal::Keyword(Keyword::new("default"))
    );
}

#[test]
fn test_sorted_set_by_predicates() {
    assert!(eval_bool("(sorted? (sorted-set-by < 1 2))"));
    assert!(eval_bool("(coll? (sorted-set-by < 1 2))"));
    assert!(eval_bool("(seqable? (sorted-set-by < 1 2))"));
    assert!(eval_bool("(counted? (sorted-set-by < 1 2))"));
}

#[test]
fn test_sorted_set_by_duplicates() {
    // Duplicates should be removed
    assert_eq!(eval_int("(count (sorted-set-by < 1 1 2 2 3 3))"), 3);
}

// =============================================================================
// Custom comparators
// =============================================================================

#[test]
fn test_boolean_comparator() {
    // Using < as a boolean comparator
    assert_eq!(
        eval_str("(keys (sorted-map-by < 3 :c 1 :a 2 :b))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_three_way_comparator() {
    // Using compare as a three-way comparator
    assert_eq!(
        eval_str("(keys (sorted-map-by compare 3 :c 1 :a 2 :b))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_custom_fn_comparator() {
    // Using a custom function as comparator
    assert_eq!(
        eval_str("(keys (sorted-map-by (fn [a b] (- b a)) 1 :a 2 :b 3 :c))").unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(2),
            KlujurVal::int(1)
        ])
    );
}
