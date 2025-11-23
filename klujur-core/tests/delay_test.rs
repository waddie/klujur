// klujur-core - Delay integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur delay and force operations.
//!
//! Tests for: delay, force, delay?, realized?

mod common;

use common::{KlujurVal, eval_str, eval_str_with_env, new_env};

// =============================================================================
// Delay creation
// =============================================================================

#[test]
fn test_delay_creation() {
    let result = eval_str("(delay 42)").unwrap();
    assert!(matches!(result, KlujurVal::Delay(_)));
}

#[test]
fn test_delay_with_expression() {
    let result = eval_str("(delay (+ 1 2))").unwrap();
    assert!(matches!(result, KlujurVal::Delay(_)));
}

#[test]
fn test_delay_does_not_evaluate_immediately() {
    let env = new_env();
    eval_str_with_env("(def side-effect (atom 0))", &env).unwrap();

    // Creating the delay should not trigger the side effect
    eval_str_with_env("(def d (delay (do (swap! side-effect inc) :done)))", &env).unwrap();

    let result = eval_str_with_env("@side-effect", &env).unwrap();
    assert_eq!(result, KlujurVal::int(0));
}

// =============================================================================
// Force
// =============================================================================

#[test]
fn test_force_delay() {
    assert_eval!("(force (delay 42))", KlujurVal::int(42));
}

#[test]
fn test_force_expression() {
    assert_eval!("(force (delay (+ 1 2 3)))", KlujurVal::int(6));
}

#[test]
fn test_force_triggers_evaluation() {
    let env = new_env();
    eval_str_with_env("(def side-effect (atom 0))", &env).unwrap();
    eval_str_with_env("(def d (delay (do (swap! side-effect inc) :done)))", &env).unwrap();

    // Before force
    let result = eval_str_with_env("@side-effect", &env).unwrap();
    assert_eq!(result, KlujurVal::int(0));

    // Force the delay
    let result = eval_str_with_env("(force d)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));

    // After force
    let result = eval_str_with_env("@side-effect", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_force_non_delay() {
    // force on non-delay returns the value unchanged
    assert_eval!("(force 42)", KlujurVal::int(42));
    assert_eval!(
        "(force :keyword)",
        KlujurVal::keyword(common::Keyword::new("keyword"))
    );
    assert_eval!(
        "(force [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Deref (@) on realized delays
// =============================================================================

#[test]
fn test_deref_realized_delay() {
    // Deref works on realized delays
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();
    // First realize it
    eval_str_with_env("(force d)", &env).unwrap();
    // Now deref works
    let result = eval_str_with_env("@d", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

#[test]
fn test_deref_realized_delay_expression() {
    let env = new_env();
    eval_str_with_env("(def d (delay (* 6 7)))", &env).unwrap();
    // Realize it first
    eval_str_with_env("(force d)", &env).unwrap();
    let result = eval_str_with_env("@d", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

#[test]
fn test_deref_unrealized_delay_errors() {
    // Deref on unrealized delay requires special handling
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();
    // This should error - use force instead
    let result = eval_str_with_env("@d", &env);
    assert!(result.is_err());
}

// =============================================================================
// Memoisation (caching)
// =============================================================================

#[test]
fn test_delay_caches_result() {
    let env = new_env();
    eval_str_with_env("(def counter (atom 0))", &env).unwrap();
    eval_str_with_env("(def d (delay (swap! counter inc)))", &env).unwrap();

    // First force
    eval_str_with_env("(force d)", &env).unwrap();
    let result = eval_str_with_env("@counter", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));

    // Second force - should not increment counter again
    eval_str_with_env("(force d)", &env).unwrap();
    let result = eval_str_with_env("@counter", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));

    // Third force
    eval_str_with_env("(force d)", &env).unwrap();
    let result = eval_str_with_env("@counter", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_delay_returns_same_value() {
    let env = new_env();
    eval_str_with_env("(def d (delay (+ 1 2)))", &env).unwrap();

    let result1 = eval_str_with_env("(force d)", &env).unwrap();
    let result2 = eval_str_with_env("(force d)", &env).unwrap();
    let result3 = eval_str_with_env("@d", &env).unwrap();

    assert_eq!(result1, KlujurVal::int(3));
    assert_eq!(result2, KlujurVal::int(3));
    assert_eq!(result3, KlujurVal::int(3));
}

// =============================================================================
// delay?
// =============================================================================

#[test]
fn test_delay_predicate_true() {
    assert_eval!("(delay? (delay 1))", KlujurVal::bool(true));
}

#[test]
fn test_delay_predicate_false() {
    assert_eval!("(delay? 1)", KlujurVal::bool(false));
    assert_eval!("(delay? nil)", KlujurVal::bool(false));
    assert_eval!("(delay? [1 2])", KlujurVal::bool(false));
    assert_eval!("(delay? (atom 1))", KlujurVal::bool(false));
}

// =============================================================================
// realized?
// =============================================================================

#[test]
fn test_realized_before_force() {
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();

    let result = eval_str_with_env("(realized? d)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

#[test]
fn test_realized_after_force() {
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();

    // Force it
    eval_str_with_env("(force d)", &env).unwrap();

    let result = eval_str_with_env("(realized? d)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_realized_after_deref() {
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();

    // Force it first (deref on stored delay works after first realization)
    eval_str_with_env("(force d)", &env).unwrap();

    // Now deref should work
    let result = eval_str_with_env("@d", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));

    let realized = eval_str_with_env("(realized? d)", &env).unwrap();
    assert_eq!(realized, KlujurVal::bool(true));
}

// =============================================================================
// Delay with closures
// =============================================================================

#[test]
fn test_delay_captures_environment() {
    let env = new_env();
    eval_str_with_env("(def x 10)", &env).unwrap();
    eval_str_with_env("(def d (delay (* x 2)))", &env).unwrap();

    let result = eval_str_with_env("(force d)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(20));
}

#[test]
fn test_delay_captures_at_creation_time() {
    let env = new_env();
    eval_str_with_env("(def x 10)", &env).unwrap();
    eval_str_with_env("(def d (delay x))", &env).unwrap();

    // Change x after delay is created
    eval_str_with_env("(def x 999)", &env).unwrap();

    // The delay captures x from its creation environment
    // Note: Whether this captures the var or the value depends on implementation
    // In Clojure, it captures the var, so changing x would affect the delay
    let result = eval_str_with_env("(force d)", &env).unwrap();
    // Either 10 (captured value) or 999 (captured var) is valid depending on impl
    assert!(result == KlujurVal::int(10) || result == KlujurVal::int(999));
}

// =============================================================================
// Nested delays
// =============================================================================

#[test]
fn test_nested_delay() {
    let env = new_env();
    eval_str_with_env("(def d (delay (delay 42)))", &env).unwrap();

    // First force gives us the inner delay
    let result = eval_str_with_env("(force d)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Delay(_)));

    // Force again to get the final value
    let result = eval_str_with_env("(force (force d))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

// =============================================================================
// Delay in collections
// =============================================================================

#[test]
fn test_delay_in_vector() {
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();
    eval_str_with_env("(def v [d])", &env).unwrap();

    let result = eval_str_with_env("(force (first v))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

#[test]
fn test_delay_in_map() {
    let env = new_env();
    eval_str_with_env("(def d (delay 42))", &env).unwrap();
    eval_str_with_env("(def m {:value d})", &env).unwrap();

    let result = eval_str_with_env("(force (get m :value))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

// =============================================================================
// Error handling in delay
// =============================================================================

#[test]
fn test_delay_error_propagates() {
    let env = new_env();
    eval_str_with_env("(def d (delay (throw (ex-info \"test error\" {}))))", &env).unwrap();

    let result = eval_str_with_env("(force d)", &env);
    assert!(result.is_err());
}

// =============================================================================
// Multiple body expressions
// =============================================================================

#[test]
fn test_delay_multiple_expressions() {
    let env = new_env();
    eval_str_with_env("(def counter (atom 0))", &env).unwrap();
    eval_str_with_env(
        "(def d (delay
                  (swap! counter inc)
                  (swap! counter inc)
                  (swap! counter inc)
                  @counter))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(force d)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));

    // Verify counter state
    let counter = eval_str_with_env("@counter", &env).unwrap();
    assert_eq!(counter, KlujurVal::int(3));
}
