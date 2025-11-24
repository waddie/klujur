// klujur-core - Property-based tests for destructuring
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Property-based tests for destructuring patterns.
//!
//! Tests the following properties:
//! - Sequential destructuring extracts correct values
//! - Map destructuring with :keys, :strs extracts correct values
//! - Nested destructuring works correctly
//! - :or defaults are applied correctly
//! - :as bindings capture the entire structure

mod common;

use common::{KlujurVal, eval_str_with_stdlib};
use proptest::prelude::*;

// =============================================================================
// Strategies for generating values
// =============================================================================

/// Generate small integers for destructuring tests
fn arb_small_int() -> impl Strategy<Value = i64> {
    -100i64..100i64
}

// =============================================================================
// Sequential destructuring tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Basic sequential: [a b c] against [1 2 3]
    #[test]
    fn sequential_basic(a in arb_small_int(), b in arb_small_int(), c in arb_small_int()) {
        let code = format!(
            "(let* [[x y z] [{} {} {}]] (+ x y z))",
            a, b, c
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b + c),
            "Sequential destructuring failed for [{} {} {}]",
            a, b, c
        );
    }

    /// Sequential with underscore: [a _ c] ignores middle
    #[test]
    fn sequential_underscore(a in arb_small_int(), b in arb_small_int(), c in arb_small_int()) {
        let code = format!(
            "(let* [[x _ z] [{} {} {}]] (+ x z))",
            a, b, c
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + c),
            "Underscore destructuring failed"
        );
    }

    /// Sequential with rest: [a & rest]
    #[test]
    fn sequential_rest(
        a in arb_small_int(),
        rest in prop::collection::vec(arb_small_int(), 0..=3)
    ) {
        let all: Vec<String> = std::iter::once(a)
            .chain(rest.iter().copied())
            .map(|n| n.to_string())
            .collect();
        let vec_str = format!("[{}]", all.join(" "));

        let code = format!(
            "(let* [[x & xs] {}] (count xs))",
            vec_str
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(rest.len() as i64),
            "Rest destructuring count incorrect for {}",
            vec_str
        );
    }

    /// Sequential with :as captures whole
    #[test]
    fn sequential_as(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [[x y :as all] [{} {}]] (count all))",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(2),
            ":as should capture entire vector"
        );
    }

    /// Shorter vector than pattern binds nil
    #[test]
    fn sequential_short_vector(a in arb_small_int()) {
        let code = format!(
            "(let* [[x y z] [{}]] (nil? z))",
            a
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::bool(true),
            "Missing elements should bind to nil"
        );
    }
}

// =============================================================================
// Associative destructuring tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// :keys destructuring
    #[test]
    fn keys_destructuring(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [{{:keys [x y]}} {{:x {} :y {}}}] (+ x y))",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            ":keys destructuring failed"
        );
    }

    /// :strs destructuring
    #[test]
    fn strs_destructuring(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            r#"(let* [{{:strs [x y]}} {{"x" {} "y" {}}}] (+ x y))"#,
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            ":strs destructuring failed"
        );
    }

    /// Explicit key binding: {foo :bar}
    #[test]
    fn explicit_key_binding(v in arb_small_int()) {
        let code = format!(
            "(let* [{{x :key}} {{:key {}}}] x)",
            v
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(v),
            "Explicit key binding failed"
        );
    }

    /// :or provides defaults for missing keys
    #[test]
    fn or_default(present in arb_small_int(), default in arb_small_int()) {
        // y is missing, should use default
        let code = format!(
            "(let* [{{:keys [x y] :or {{y {}}}}} {{:x {}}}] (+ x y))",
            default, present
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(present + default),
            ":or default not applied"
        );
    }

    /// :or doesn't override present keys
    #[test]
    fn or_no_override(actual in arb_small_int(), default in arb_small_int()) {
        let code = format!(
            "(let* [{{:keys [x] :or {{x {}}}}} {{:x {}}}] x)",
            default, actual
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(actual),
            ":or should not override present key"
        );
    }

    /// :as in map destructuring captures whole map
    #[test]
    fn map_as(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [{{:keys [x] :as m}} {{:x {} :y {}}}] (count m))",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(2),
            ":as should capture entire map"
        );
    }
}

// =============================================================================
// Nested destructuring tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// Nested sequential: [[a b] [c d]]
    #[test]
    fn nested_sequential(a in arb_small_int(), b in arb_small_int(), c in arb_small_int(), d in arb_small_int()) {
        let code = format!(
            "(let* [[[x y] [z w]] [[{} {}] [{} {}]]] (+ x y z w))",
            a, b, c, d
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b + c + d),
            "Nested sequential destructuring failed"
        );
    }

    /// Map inside vector: [{:keys [x]}]
    #[test]
    fn map_in_vector(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [[{{:keys [x]}} {{:keys [y]}}] [{{:x {}}} {{:y {}}}]] (+ x y))",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            "Map in vector destructuring failed"
        );
    }

    /// Vector inside map: {:pair [a b]}
    #[test]
    fn vector_in_map(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [{{[x y] :pair}} {{:pair [{} {}]}}] (+ x y))",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            "Vector in map destructuring failed"
        );
    }
}

// =============================================================================
// Round-trip property tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// Destructure and reconstruct vector preserves values
    #[test]
    fn vector_roundtrip(a in arb_small_int(), b in arb_small_int(), c in arb_small_int()) {
        let code = format!(
            "(let* [[x y z] [{} {} {}]] [x y z])",
            a, b, c
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        let expected = eval_str_with_stdlib(&format!("[{} {} {}]", a, b, c)).unwrap();
        prop_assert_eq!(result, expected, "Vector roundtrip failed");
    }

    /// Destructure and reconstruct map preserves values
    #[test]
    fn map_roundtrip(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [{{:keys [x y]}} {{:x {} :y {}}}] {{:x x :y y}})",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        let expected = eval_str_with_stdlib(&format!("{{:x {} :y {}}}", a, b)).unwrap();
        prop_assert_eq!(result, expected, "Map roundtrip failed");
    }

    /// :as binding equals original value
    #[test]
    fn as_equals_original(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "(let* [[x y :as all] [{} {}]] (= all [{} {}]))",
            a, b, a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), ":as binding should equal original");
    }
}

// =============================================================================
// Function argument destructuring
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// fn with sequential destructuring
    #[test]
    fn fn_sequential_destructure(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "((fn [[x y]] (+ x y)) [{} {}])",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            "fn sequential destructuring failed"
        );
    }

    /// fn with map destructuring
    #[test]
    fn fn_map_destructure(a in arb_small_int(), b in arb_small_int()) {
        let code = format!(
            "((fn [{{:keys [x y]}}] (+ x y)) {{:x {} :y {}}})",
            a, b
        );
        let result = eval_str_with_stdlib(&code).unwrap();
        prop_assert_eq!(
            result,
            KlujurVal::int(a + b),
            "fn map destructuring failed"
        );
    }
}

// =============================================================================
// Edge cases
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Destructuring nil gives nil bindings
    #[test]
    fn destructure_nil(_dummy in 0..1i32) {
        let code = "(let* [[x y] nil] (and (nil? x) (nil? y)))";
        let result = eval_str_with_stdlib(code).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "Destructuring nil should bind nil");
    }

    /// Empty vector destructuring
    #[test]
    fn destructure_empty_vector(_dummy in 0..1i32) {
        let code = "(let* [[x y] []] (and (nil? x) (nil? y)))";
        let result = eval_str_with_stdlib(code).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "Destructuring empty vector should bind nil");
    }

    /// Empty map destructuring
    #[test]
    fn destructure_empty_map(_dummy in 0..1i32) {
        let code = "(let* [{:keys [x y]} {}] (and (nil? x) (nil? y)))";
        let result = eval_str_with_stdlib(code).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "Destructuring empty map should bind nil");
    }
}
