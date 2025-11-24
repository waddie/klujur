// klujur-core - Property-based tests for collection operations
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Property-based tests for collection operations and invariants.
//!
//! Tests the following properties:
//! - cons/first/rest round-trips
//! - conj/count invariants
//! - assoc/get round-trips for maps
//! - contains?/conj for sets
//! - Sequence operation consistency

mod common;

use common::{KlujurVal, eval_str, eval_str_with_env, eval_str_with_stdlib, new_env};
use proptest::prelude::*;

// =============================================================================
// Strategies for generating values
// =============================================================================

/// Generate small integers for collection elements
fn arb_small_int() -> impl Strategy<Value = i64> {
    -1000i64..1000i64
}

/// Generate small vectors (as Klujur code strings)
fn arb_int_vector(max_len: usize) -> impl Strategy<Value = String> {
    prop::collection::vec(arb_small_int(), 0..=max_len).prop_map(|v| {
        let elements: Vec<String> = v.iter().map(|n| n.to_string()).collect();
        format!("[{}]", elements.join(" "))
    })
}

/// Generate small lists (as Klujur code strings)
fn arb_int_list(max_len: usize) -> impl Strategy<Value = String> {
    prop::collection::vec(arb_small_int(), 0..=max_len).prop_map(|v| {
        let elements: Vec<String> = v.iter().map(|n| n.to_string()).collect();
        format!("'({})", elements.join(" "))
    })
}

/// Generate simple string keys for maps
fn arb_string_key() -> impl Strategy<Value = String> {
    "[a-z]{1,5}".prop_map(|s| format!("\"{}\"", s))
}

// =============================================================================
// cons/first/rest round-trip tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// (first (cons x coll)) = x
    #[test]
    fn cons_first_identity(x in arb_small_int(), coll in arb_int_vector(5)) {
        let env = new_env();
        let code = format!("(first (cons {} {}))", x, coll);
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(x),
            "cons/first identity failed: {}",
            code
        );
    }

    /// (rest (cons x coll)) produces elements equivalent to coll
    /// For non-empty coll: count should be preserved
    #[test]
    fn cons_rest_preserves_count(x in arb_small_int(), coll in arb_int_vector(5)) {
        let env = new_env();

        // Get original count
        let orig_count = eval_str_with_env(&format!("(count {})", coll), &env).unwrap();

        // Get count after cons then rest
        let after_count = eval_str_with_env(
            &format!("(count (rest (cons {} {})))", x, coll),
            &env
        ).unwrap();

        prop_assert_eq!(
            orig_count,
            after_count,
            "cons/rest should preserve count for coll={}",
            coll
        );
    }

    /// first of empty collection is nil
    #[test]
    fn first_empty_is_nil(_dummy in 0..1i32) {
        let result = eval_str("(first [])").unwrap();
        prop_assert_eq!(result, KlujurVal::Nil, "first of empty vector should be nil");

        let result = eval_str("(first '())").unwrap();
        prop_assert_eq!(result, KlujurVal::Nil, "first of empty list should be nil");
    }

    /// rest of empty collection is empty list
    #[test]
    fn rest_empty_is_empty_list(_dummy in 0..1i32) {
        let result = eval_str("(rest [])").unwrap();
        prop_assert!(matches!(result, KlujurVal::List(v, _) if v.is_empty()),
            "rest of empty vector should be empty list");

        let result = eval_str("(rest '())").unwrap();
        prop_assert!(matches!(result, KlujurVal::List(v, _) if v.is_empty()),
            "rest of empty list should be empty list");
    }

    /// next of single-element collection is nil
    #[test]
    fn next_single_is_nil(x in arb_small_int()) {
        let result = eval_str(&format!("(next [{}])", x)).unwrap();
        prop_assert_eq!(result, KlujurVal::Nil, "next of single-element vector should be nil");
    }
}

// =============================================================================
// conj/count invariants
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// (count (conj coll x)) = (+ 1 (count coll)) for vectors
    #[test]
    fn conj_increments_count_vector(x in arb_small_int(), coll in arb_int_vector(5)) {
        let env = new_env();

        let orig_count = eval_str_with_env(&format!("(count {})", coll), &env).unwrap();
        let new_count = eval_str_with_env(
            &format!("(count (conj {} {}))", coll, x),
            &env
        ).unwrap();

        let expected = match orig_count {
            KlujurVal::Int(n) => KlujurVal::int(n + 1),
            _ => panic!("count should return int"),
        };

        prop_assert_eq!(new_count, expected, "conj should increment count");
    }

    /// (count (conj coll x)) = (+ 1 (count coll)) for lists
    #[test]
    fn conj_increments_count_list(x in arb_small_int(), coll in arb_int_list(5)) {
        let env = new_env();

        let orig_count = eval_str_with_env(&format!("(count {})", coll), &env).unwrap();
        let new_count = eval_str_with_env(
            &format!("(count (conj {} {}))", coll, x),
            &env
        ).unwrap();

        let expected = match orig_count {
            KlujurVal::Int(n) => KlujurVal::int(n + 1),
            _ => panic!("count should return int"),
        };

        prop_assert_eq!(new_count, expected, "conj should increment count for lists");
    }

    /// conj to vector adds at the end
    #[test]
    fn conj_vector_adds_at_end(x in arb_small_int(), coll in arb_int_vector(5)) {
        let env = new_env();

        let last_elem = eval_str_with_env(
            &format!("(last (conj {} {}))", coll, x),
            &env
        ).unwrap();

        prop_assert_eq!(last_elem, KlujurVal::int(x), "conj to vector should add at end");
    }

    /// conj to list adds at the front
    #[test]
    fn conj_list_adds_at_front(x in arb_small_int(), coll in arb_int_list(5)) {
        let env = new_env();

        let first_elem = eval_str_with_env(
            &format!("(first (conj {} {}))", coll, x),
            &env
        ).unwrap();

        prop_assert_eq!(first_elem, KlujurVal::int(x), "conj to list should add at front");
    }
}

// =============================================================================
// Map operations: assoc/get round-trips
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// (get (assoc m k v) k) = v
    #[test]
    fn assoc_get_roundtrip(k in arb_string_key(), v in arb_small_int()) {
        let env = new_env();
        let code = format!("(get (assoc {{}} {} {}) {})", k, v, k);
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::int(v), "assoc/get roundtrip failed");
    }

    /// assoc overwrites existing key
    #[test]
    fn assoc_overwrites(k in arb_string_key(), v1 in arb_small_int(), v2 in arb_small_int()) {
        let env = new_env();
        let code = format!(
            "(get (assoc (assoc {{}} {} {}) {} {}) {})",
            k, v1, k, v2, k
        );
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::int(v2), "assoc should overwrite existing key");
    }

    /// (count (assoc m k v)) = (count m) or (+ 1 (count m))
    #[test]
    fn assoc_count_invariant(k in arb_string_key(), v in arb_small_int()) {
        let env = new_env();

        // Start with empty map
        let before = eval_str_with_env("(count {})", &env).unwrap();
        let after = eval_str_with_env(&format!("(count (assoc {{}} {} {}))", k, v), &env).unwrap();

        // For new key, count increases by 1
        let expected = match before {
            KlujurVal::Int(n) => KlujurVal::int(n + 1),
            _ => panic!("count should return int"),
        };

        prop_assert_eq!(after, expected, "assoc should increase count for new key");
    }

    /// dissoc removes key
    #[test]
    fn dissoc_removes_key(k in arb_string_key(), v in arb_small_int()) {
        let env = new_env();
        let code = format!(
            "(get (dissoc (assoc {{}} {} {}) {}) {})",
            k, v, k, k
        );
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::Nil, "dissoc should remove key");
    }

    /// contains? is true after assoc
    #[test]
    fn contains_after_assoc(k in arb_string_key(), v in arb_small_int()) {
        let env = new_env();
        let code = format!("(contains? (assoc {{}} {} {}) {})", k, v, k);
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "contains? should be true after assoc");
    }
}

// =============================================================================
// Set operations
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// (contains? (conj set x) x) = true
    #[test]
    fn set_conj_contains(x in arb_small_int()) {
        let env = new_env();
        let code = format!("(contains? (conj #{{}} {}) {})", x, x);
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "set should contain element after conj");
    }

    /// conj of duplicate doesn't increase count
    #[test]
    fn set_conj_idempotent(x in arb_small_int()) {
        let env = new_env();

        let once = eval_str_with_env(&format!("(count (conj #{{}} {}))", x), &env).unwrap();
        let twice = eval_str_with_env(&format!("(count (conj (conj #{{}} {}) {}))", x, x), &env).unwrap();

        prop_assert_eq!(once, twice, "conj of duplicate should not increase set count");
    }

    /// disj removes element from set
    #[test]
    fn set_disj_removes(x in arb_small_int()) {
        let env = new_env();
        let code = format!("(contains? (disj (conj #{{}} {}) {}) {})", x, x, x);
        let result = eval_str_with_env(&code, &env).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(false), "disj should remove element from set");
    }
}

// =============================================================================
// Sequence operation consistency
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// (into [] coll) preserves count
    #[test]
    fn into_preserves_count(coll in arb_int_list(5)) {
        let env = new_env();

        let orig = eval_str_with_env(&format!("(count {})", coll), &env).unwrap();
        let after = eval_str_with_env(&format!("(count (into [] {}))", coll), &env).unwrap();

        prop_assert_eq!(orig, after, "into [] should preserve count");
    }

    /// (vec coll) preserves count
    #[test]
    fn vec_preserves_count(coll in arb_int_list(5)) {
        let env = new_env();

        let orig = eval_str_with_env(&format!("(count {})", coll), &env).unwrap();
        let after = eval_str_with_env(&format!("(count (vec {}))", coll), &env).unwrap();

        prop_assert_eq!(orig, after, "vec should preserve count");
    }

    /// reverse twice is identity
    #[test]
    fn reverse_twice_identity(coll in arb_int_vector(5)) {
        let env = new_env();

        // Compare as vectors to ensure order
        let original = eval_str_with_env(&format!("(vec {})", coll), &env).unwrap();
        let twice = eval_str_with_env(&format!("(vec (reverse (reverse {})))", coll), &env).unwrap();

        prop_assert_eq!(original, twice, "reverse twice should be identity");
    }

    /// (count (take n coll)) <= n (requires stdlib for take)
    #[test]
    fn take_count_bounded(n in 0usize..10, coll in arb_int_vector(10)) {
        let result = eval_str_with_stdlib(
            &format!("(count (take {} {}))", n, coll),
        ).unwrap();

        if let KlujurVal::Int(count) = result {
            prop_assert!(count as usize <= n, "take {} should produce at most {} elements", n, n);
        } else {
            prop_assert!(false, "count should return int");
        }
    }

    /// (count (drop n coll)) = max(0, (count coll) - n) (requires stdlib for drop)
    #[test]
    fn drop_count_correct(n in 0usize..10, coll in arb_int_vector(10)) {
        let orig_count = eval_str_with_stdlib(&format!("(count {})", coll)).unwrap();
        let drop_count = eval_str_with_stdlib(&format!("(count (drop {} {}))", n, coll)).unwrap();

        if let (KlujurVal::Int(orig), KlujurVal::Int(dropped)) = (orig_count, drop_count) {
            let expected = (orig as usize).saturating_sub(n) as i64;
            prop_assert_eq!(dropped, expected, "drop count incorrect for n={}, coll={}", n, coll);
        } else {
            prop_assert!(false, "count should return int");
        }
    }
}

// =============================================================================
// nth/get for indexed access
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// nth returns correct element (for valid indices)
    #[test]
    fn nth_correct_element(
        elements in prop::collection::vec(arb_small_int(), 1..=5),
        idx_offset in 0usize..5
    ) {
        let idx = idx_offset % elements.len();
        let coll_str = format!("[{}]", elements.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(" "));

        let env = new_env();
        let result = eval_str_with_env(&format!("(nth {} {})", coll_str, idx), &env).unwrap();

        prop_assert_eq!(
            result,
            KlujurVal::int(elements[idx]),
            "nth {} {} should return {}",
            coll_str,
            idx,
            elements[idx]
        );
    }

    /// get with default returns default for out-of-bounds
    #[test]
    fn get_default_for_missing(coll in arb_int_vector(3), default in arb_small_int()) {
        let env = new_env();

        // Use an index that's definitely out of bounds
        let result = eval_str_with_env(
            &format!("(get {} 9999 {})", coll, default),
            &env
        ).unwrap();

        prop_assert_eq!(result, KlujurVal::int(default), "get should return default for missing index");
    }
}
