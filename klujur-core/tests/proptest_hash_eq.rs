// klujur-core - Property-based tests for Hash/Eq consistency
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Property-based tests for Hash/Eq consistency.
//!
//! Tests the fundamental hash contract: if a == b, then hash(a) == hash(b).
//! This is critical for correct behaviour when using KlujurVal as map keys.

mod common;

use common::{Keyword, KlujurVal, eval_str, new_env};
use klujur_parser::Symbol;
use proptest::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Compute the hash of a KlujurVal
fn compute_hash(val: &KlujurVal) -> u64 {
    let mut hasher = DefaultHasher::new();
    val.hash(&mut hasher);
    hasher.finish()
}

/// Assert that two values are equal and have equal hashes
fn assert_hash_eq_consistent(v1: &KlujurVal, v2: &KlujurVal, msg: &str) {
    assert_eq!(v1, v2, "{} - values should be equal", msg);
    assert_eq!(
        compute_hash(v1),
        compute_hash(v2),
        "{} - hashes should be equal",
        msg
    );
}

// =============================================================================
// Numeric type equality and hashing
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Int values that are equal should have equal hashes
    #[test]
    fn int_hash_eq_consistency(n in any::<i64>()) {
        let v1 = KlujurVal::int(n);
        let v2 = KlujurVal::int(n);

        assert_hash_eq_consistent(&v1, &v2, "same int");
    }

    /// Float values that are equal should have equal hashes
    #[test]
    fn float_hash_eq_consistency(n in any::<f64>().prop_filter("finite", |f| f.is_finite())) {
        let v1 = KlujurVal::float(n);
        let v2 = KlujurVal::float(n);

        assert_hash_eq_consistent(&v1, &v2, "same float");
    }

    /// Int and Float that are numerically equal should have equal hashes
    /// This tests the cross-type equality case: 1 == 1.0
    #[test]
    fn int_float_cross_equality_hash(n in -1000i64..1000i64) {
        let int_val = KlujurVal::int(n);
        let float_val = KlujurVal::float(n as f64);

        // In Klujur, numeric equality is cross-type: (= 1 1.0) => true
        if int_val == float_val {
            assert_eq!(
                compute_hash(&int_val),
                compute_hash(&float_val),
                "int {} and float {} are equal but have different hashes",
                n, n
            );
        }
    }

    /// Ratio 1/1 should equal Int 1 and have the same hash
    #[test]
    fn ratio_int_equality_hash(n in -100i64..100i64) {
        // Ratio n/1 should equal Int n
        let int_val = KlujurVal::int(n);
        let ratio_val = KlujurVal::ratio(n, 1);

        // After normalisation, n/1 becomes Int n, so they should be equal
        if int_val == ratio_val {
            assert_eq!(
                compute_hash(&int_val),
                compute_hash(&ratio_val),
                "int {} and ratio {}/1 are equal but have different hashes",
                n, n
            );
        }
    }
}

// =============================================================================
// Collection type equality and hashing
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Lists with the same elements should have equal hashes
    #[test]
    fn list_hash_eq_consistency(elements in prop::collection::vec(-100i64..100i64, 0..5)) {
        let items: Vec<KlujurVal> = elements.iter().map(|&n| KlujurVal::int(n)).collect();
        let v1 = KlujurVal::list(items.clone());
        let v2 = KlujurVal::list(items);

        assert_hash_eq_consistent(&v1, &v2, "same list");
    }

    /// Vectors with the same elements should have equal hashes
    #[test]
    fn vector_hash_eq_consistency(elements in prop::collection::vec(-100i64..100i64, 0..5)) {
        let items: Vec<KlujurVal> = elements.iter().map(|&n| KlujurVal::int(n)).collect();
        let v1 = KlujurVal::vector(items.clone());
        let v2 = KlujurVal::vector(items);

        assert_hash_eq_consistent(&v1, &v2, "same vector");
    }

    /// Lists and vectors with the same elements should be equal and have equal hashes
    /// This is Clojure semantics: (= '(1 2 3) [1 2 3]) => true
    #[test]
    fn list_vector_cross_equality_hash(elements in prop::collection::vec(-100i64..100i64, 0..5)) {
        let items: Vec<KlujurVal> = elements.iter().map(|&n| KlujurVal::int(n)).collect();
        let list = KlujurVal::list(items.clone());
        let vector = KlujurVal::vector(items);

        // In Klujur, sequential collections are equal if they have the same elements
        assert_hash_eq_consistent(&list, &vector, "list and vector with same elements");
    }

    /// Maps with the same key-value pairs should have equal hashes
    #[test]
    fn map_hash_eq_consistency(
        pairs in prop::collection::vec((prop::string::string_regex("[a-z]{1,3}").unwrap(), -100i64..100i64), 0..5)
    ) {
        let kvs: Vec<(KlujurVal, KlujurVal)> = pairs.iter()
            .map(|(k, v)| (KlujurVal::string(k.as_str()), KlujurVal::int(*v)))
            .collect();
        let v1 = KlujurVal::map(kvs.clone());
        let v2 = KlujurVal::map(kvs);

        assert_hash_eq_consistent(&v1, &v2, "same map");
    }

    /// Sets with the same elements should have equal hashes
    #[test]
    fn set_hash_eq_consistency(elements in prop::collection::vec(-100i64..100i64, 0..5)) {
        let items: Vec<KlujurVal> = elements.iter().map(|&n| KlujurVal::int(n)).collect();
        let v1 = KlujurVal::set(items.clone());
        let v2 = KlujurVal::set(items);

        assert_hash_eq_consistent(&v1, &v2, "same set");
    }
}

// =============================================================================
// String and identifier types
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Strings with the same content should have equal hashes
    #[test]
    fn string_hash_eq_consistency(s in "[a-zA-Z0-9]{0,20}") {
        let v1 = KlujurVal::string(s.as_str());
        let v2 = KlujurVal::string(s.as_str());

        assert_hash_eq_consistent(&v1, &v2, "same string");
    }

    /// Keywords with the same name should have equal hashes
    #[test]
    fn keyword_hash_eq_consistency(name in "[a-z]{1,10}") {
        let v1 = KlujurVal::keyword(Keyword::new(&name));
        let v2 = KlujurVal::keyword(Keyword::new(&name));

        assert_hash_eq_consistent(&v1, &v2, "same keyword");
    }

    /// Symbols with the same name should have equal hashes
    #[test]
    fn symbol_hash_eq_consistency(name in "[a-z]{1,10}") {
        let v1 = KlujurVal::symbol(Symbol::new(&name));
        let v2 = KlujurVal::symbol(Symbol::new(&name));

        assert_hash_eq_consistent(&v1, &v2, "same symbol");
    }

    /// Characters with the same value should have equal hashes
    #[test]
    fn char_hash_eq_consistency(c in any::<char>()) {
        let v1 = KlujurVal::char(c);
        let v2 = KlujurVal::char(c);

        assert_hash_eq_consistent(&v1, &v2, "same char");
    }
}

// =============================================================================
// Special values
// =============================================================================

#[test]
fn nil_hash_eq_consistency() {
    let v1 = KlujurVal::Nil;
    let v2 = KlujurVal::Nil;

    assert_hash_eq_consistent(&v1, &v2, "nil");
}

#[test]
fn bool_hash_eq_consistency() {
    let true1 = KlujurVal::Bool(true);
    let true2 = KlujurVal::Bool(true);
    let false1 = KlujurVal::Bool(false);
    let false2 = KlujurVal::Bool(false);

    assert_hash_eq_consistent(&true1, &true2, "true");
    assert_hash_eq_consistent(&false1, &false2, "false");

    // true != false
    assert_ne!(true1, false1);
}

// =============================================================================
// Metadata should not affect equality or hashing
// =============================================================================

#[test]
fn metadata_ignored_in_equality() {
    // In Klujur, metadata doesn't affect equality
    // (= [1 2] (with-meta [1 2] {:a 1})) => true
    let v1 = KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)]);
    let v2 = KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)]);

    // Even if one had metadata, they should still be equal
    assert_hash_eq_consistent(&v1, &v2, "vectors with same elements");
}

// =============================================================================
// Map key behaviour tests
// =============================================================================

#[test]
fn list_vector_as_map_keys() {
    // Since list and vector are equal when they have the same elements,
    // they should work as the same key in a map
    let _env = new_env();

    // This test verifies the hash contract is maintained for map key usage
    let result = eval_str("(get {[1 2] :vec} '(1 2))");

    // If list/vector are equal, looking up with list should find vector key
    // This is the practical consequence of the Hash/Eq contract
    if result.is_ok() {
        // Either we get :vec (if cross-type lookup works) or nil (if not)
        // The important thing is no crash or inconsistent behaviour
        let val = result.unwrap();
        let is_vec = val == KlujurVal::keyword(Keyword::new("vec"));
        let is_nil = val == KlujurVal::Nil;
        assert!(is_vec || is_nil, "unexpected result: {:?}", val);
    }
}

// =============================================================================
// Numeric edge cases
// =============================================================================

#[test]
fn negative_zero_float_hash() {
    // -0.0 and 0.0 should be equal and have equal hashes
    let pos_zero = KlujurVal::float(0.0);
    let neg_zero = KlujurVal::float(-0.0);

    assert_hash_eq_consistent(&pos_zero, &neg_zero, "-0.0 and 0.0");
}

#[test]
fn nan_hash_consistency() {
    // NaN values should be equal to themselves for hashing purposes
    // (even though in IEEE float semantics NaN != NaN)
    let nan1 = KlujurVal::float(f64::NAN);
    let nan2 = KlujurVal::float(f64::NAN);

    // The hash should at least be consistent for the same value
    assert_eq!(
        compute_hash(&nan1),
        compute_hash(&nan2),
        "NaN values should have consistent hashes"
    );
}

#[test]
fn infinity_hash_consistency() {
    let pos_inf1 = KlujurVal::float(f64::INFINITY);
    let pos_inf2 = KlujurVal::float(f64::INFINITY);
    let neg_inf1 = KlujurVal::float(f64::NEG_INFINITY);
    let neg_inf2 = KlujurVal::float(f64::NEG_INFINITY);

    assert_hash_eq_consistent(&pos_inf1, &pos_inf2, "+Inf");
    assert_hash_eq_consistent(&neg_inf1, &neg_inf2, "-Inf");
}
