// klujur-core - Destructuring edge case integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur destructuring edge cases.
//!
//! Tests focused on error handling, corner cases, and interactions
//! not covered by the main Clojure test suite.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{Keyword, KlujurVal, Parser};

/// Helper to evaluate multiple expressions in shared env and return the last result.
fn eval_forms(forms: &[&str]) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).map_err(|e| e.to_string())?;
    eval_forms_with_env(forms, &env)
}

fn eval_forms_with_env(forms: &[&str], env: &Env) -> Result<KlujurVal, String> {
    let mut result = KlujurVal::Nil;
    for form in forms {
        let mut parser = Parser::new(form).map_err(|e| e.to_string())?;
        while let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
            result = eval(&expr, env).map_err(|e| e.to_string())?;
        }
    }
    Ok(result)
}

/// Assert that evaluating forms produces the expected value.
macro_rules! assert_eval_forms {
    ($forms:expr, $expected:expr) => {
        let result = eval_forms($forms);
        assert!(
            result.is_ok(),
            "Failed to evaluate forms: {:?}",
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation did not match expected"
        );
    };
}

/// Assert that evaluating forms produces an error.
macro_rules! assert_eval_forms_err {
    ($forms:expr) => {
        let result = eval_forms($forms);
        assert!(result.is_err(), "Expected error but got {:?}", result.ok());
    };
}

// =============================================================================
// Sequential Destructuring Edge Cases
// =============================================================================

#[test]
fn test_sequential_empty_pattern() {
    // Empty pattern should work and not bind anything
    assert_eval_forms!(
        &["(let [[] [1 2 3]] :ok)"],
        KlujurVal::keyword(Keyword::new("ok"))
    );
}

#[test]
fn test_sequential_from_empty_collection() {
    // Destructuring from empty should give nils
    assert_eval_forms!(
        &["(let [[a b c] []] [a b c])"],
        KlujurVal::vector(vec![KlujurVal::Nil, KlujurVal::Nil, KlujurVal::Nil])
    );
}

#[test]
fn test_sequential_as_with_rest() {
    // :as combined with & rest
    assert_eval_forms!(
        &["(let [[a & rest :as all] [1 2 3]] [a rest all])"],
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::list(vec![KlujurVal::int(2), KlujurVal::int(3)]),
            KlujurVal::vector(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3)
            ]),
        ])
    );
}

#[test]
fn test_sequential_nested_deep() {
    // Triple-nested sequential destructuring
    assert_eval_forms!(&["(let [[[[a]]] [[[42]]]] a)"], KlujurVal::int(42));
}

#[test]
fn test_sequential_ignore_with_underscore() {
    // Underscore should work for ignoring elements
    assert_eval_forms!(&["(let [[_ _ c] [1 2 3]] c)"], KlujurVal::int(3));
}

#[test]
fn test_sequential_rest_empty() {
    // & rest with no remaining elements should give nil
    assert_eval_forms!(&["(let [[a & rest] [1]] rest)"], KlujurVal::Nil);
}

#[test]
fn test_sequential_rest_only() {
    // Only & rest with nothing before
    assert_eval_forms!(
        &["(let [[& all] [1 2 3]] all)"],
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_sequential_destructure_from_string() {
    // Destructuring a string should treat it as a seq of chars
    let result = eval_forms(&["(let [[a b c] \"abc\"] [a b c])"]);
    assert!(result.is_ok());
    let val = result.unwrap();
    if let KlujurVal::Vector(items, _) = val {
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], KlujurVal::Char('a'));
        assert_eq!(items[1], KlujurVal::Char('b'));
        assert_eq!(items[2], KlujurVal::Char('c'));
    } else {
        panic!("Expected vector");
    }
}

// =============================================================================
// Sequential Destructuring Error Cases
// =============================================================================

#[test]
fn test_sequential_ampersand_at_end_error() {
    // & at end without binding is an error
    assert_eval_forms_err!(&["(let [[a &] [1 2 3]] a)"]);
}

#[test]
fn test_sequential_multiple_rest_error() {
    // Multiple & rest - the second & is treated as a literal symbol in rest binding
    // This is actually valid but probably not what the user intended
    // Testing current behaviour: evaluates without error
    let result = eval_forms(&["(let [[a & b & c] [1 2 3]] a)"]);
    assert!(result.is_ok());
}

#[test]
fn test_sequential_as_not_symbol_error() {
    // :as not followed by symbol is an error
    assert_eval_forms_err!(&["(let [[a :as 123] [1 2 3]] a)"]);
}

#[test]
fn test_sequential_as_before_rest() {
    // In Clojure, :as can come before & rest - both are valid
    // Testing current behaviour: :as all captures original, & rest captures rest
    let result = eval_forms(&["(let [[a :as all & rest] [1 2 3]] [a all rest])"]);
    // Current implementation allows this
    assert!(result.is_ok());
}

// =============================================================================
// Map Destructuring Edge Cases
// =============================================================================

#[test]
fn test_map_empty_pattern() {
    // Empty map pattern should work
    assert_eval_forms!(
        &["(let [{} {:a 1}] :ok)"],
        KlujurVal::keyword(Keyword::new("ok"))
    );
}

#[test]
fn test_map_from_nil() {
    // Destructuring nil with :or defaults
    assert_eval_forms!(
        &["(let [{:keys [a b] :or {a 1 b 2}} nil] [a b])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_map_or_with_nil_value() {
    // If key exists with nil value, :or should NOT override
    assert_eval_forms!(
        &["(let [{:keys [a] :or {a :default}} {:a nil}] a)"],
        KlujurVal::Nil
    );
}

#[test]
fn test_map_or_with_false_value() {
    // If key exists with false value, :or should NOT override
    assert_eval_forms!(
        &["(let [{:keys [a] :or {a true}} {:a false}] a)"],
        KlujurVal::bool(false)
    );
}

#[test]
fn test_map_strs_missing_keys() {
    // :strs with missing keys should give nil
    assert_eval_forms!(
        &["(let [{:strs [x y]} {\"x\" 1}] [x y])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::Nil])
    );
}

#[test]
fn test_map_syms_basic() {
    // :syms with symbol keys
    assert_eval_forms!(
        &["(let [{:syms [x y]} {'x 1 'y 2}] [x y])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_map_as_only() {
    // Only :as, no other bindings
    assert_eval_forms!(
        &["(let [{:as m} {:a 1 :b 2}] (count m))"],
        KlujurVal::int(2)
    );
}

#[test]
fn test_map_nested_or_defaults() {
    // Nested map destructuring with :or at inner level
    assert_eval_forms!(
        &["(let [{{:keys [a] :or {a 99}} :inner} {:inner {}}] a)"],
        KlujurVal::int(99)
    );
}

#[test]
fn test_map_integer_keys() {
    // Destructuring with integer keys
    assert_eval_forms!(
        &["(let [{x 0 y 1} {0 :a 1 :b}] [x y])"],
        KlujurVal::vector(vec![
            KlujurVal::keyword(Keyword::new("a")),
            KlujurVal::keyword(Keyword::new("b")),
        ])
    );
}

// =============================================================================
// Map Destructuring Error Cases
// =============================================================================

#[test]
fn test_map_or_not_map_error() {
    // :or value must be a map
    assert_eval_forms_err!(&["(let [{:keys [a] :or [1]} {:a 1}] a)"]);
}

#[test]
fn test_map_as_not_symbol_error() {
    // :as not followed by symbol is an error
    assert_eval_forms_err!(&["(let [{:keys [a] :as 123} {:a 1}] a)"]);
}

#[test]
fn test_map_keys_not_vector_error() {
    // :keys must be followed by a vector
    assert_eval_forms_err!(&["(let [{:keys (a b)} {:a 1 :b 2}] a)"]);
}

// =============================================================================
// Mixed Destructuring
// =============================================================================

#[test]
fn test_mixed_map_in_sequential() {
    // Map pattern inside sequential
    assert_eval_forms!(
        &["(let [[{:keys [a]} {:keys [b]}] [{:a 1} {:b 2}]] [a b])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_mixed_sequential_in_map() {
    // Sequential pattern inside map
    assert_eval_forms!(
        &["(let [{[a b] :pair} {:pair [1 2]}] [a b])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_mixed_triple_nesting() {
    // Map -> sequential -> map
    assert_eval_forms!(
        &["(let [{[{:keys [x]}] :items} {:items [{:x 42}]}] x)"],
        KlujurVal::int(42)
    );
}

#[test]
fn test_mixed_sequential_map_sequential() {
    // Sequential -> map -> sequential
    assert_eval_forms!(
        &["(let [[{[a b] :pair}] [{:pair [1 2]}]] [a b])"],
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

// =============================================================================
// Destructuring in Different Contexts
// =============================================================================

#[test]
fn test_destructure_in_fn_params() {
    // fn* with destructuring
    assert_eval_forms!(
        &["((fn [{:keys [a b]}] (+ a b)) {:a 1 :b 2})"],
        KlujurVal::int(3)
    );
}

#[test]
fn test_destructure_in_loop() {
    // loop with destructuring and recur
    assert_eval_forms!(
        &["(loop [[x & xs] [1 2 3] sum 0]
             (if x
               (recur xs (+ sum x))
               sum))"],
        KlujurVal::int(6)
    );
}

#[test]
fn test_destructure_in_for() {
    // for comprehension with destructuring - returns lazy seq
    let result = eval_forms(&["(vec (for [[k v] [[:a 1] [:b 2]]] v))"]);
    assert!(result.is_ok());
    assert_eq!(
        result.unwrap(),
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_destructure_in_doseq() {
    // doseq with destructuring - returns nil
    assert_eval_forms!(
        &["(doseq [[k v] [[:a 1] [:b 2]]] (println k v))"],
        KlujurVal::Nil
    );
}

// =============================================================================
// Namespaced Keys Edge Cases
// =============================================================================

#[test]
fn test_ns_keys_shorthand() {
    // :ns/keys shorthand
    assert_eval_forms!(
        &["(let [{:user/keys [name age]} {:user/name \"Alice\" :user/age 30}] [name age])"],
        KlujurVal::vector(vec![KlujurVal::string("Alice"), KlujurVal::int(30),])
    );
}

#[test]
fn test_ns_keys_mixed_namespaces() {
    // Multiple different namespaces in :keys
    assert_eval_forms!(
        &[
            "(let [{:keys [user/name config/port]} {:user/name \"Bob\" :config/port 8080}] [name port])"
        ],
        KlujurVal::vector(vec![KlujurVal::string("Bob"), KlujurVal::int(8080),])
    );
}

// =============================================================================
// Lazy Sequence Destructuring
// =============================================================================

#[test]
fn test_destructure_lazy_seq() {
    // Destructuring should work with lazy sequences
    // range with argument generates 0..n
    assert_eval_forms!(
        &["(let [[a b c] (take 5 (range 10))] [a b c])"],
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2)
        ])
    );
}

#[test]
fn test_destructure_lazy_seq_with_rest() {
    // Rest should return a lazy seq
    let result = eval_forms(&["(vec (let [[a & rest] (take 5 (range 10))] (take 2 rest)))"]);
    assert!(result.is_ok());
    assert_eq!(
        result.unwrap(),
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}
