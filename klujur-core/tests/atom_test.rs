// klujur-core - Atom integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur atoms and atomic operations.
//!
//! Tests for: atom, deref, swap!, reset!, compare-and-set!, atom?

mod common;

use common::{KlujurVal, eval_str, eval_str_with_env, new_env};

// =============================================================================
// Atom creation
// =============================================================================

#[test]
fn test_atom_creation() {
    let result = eval_str("(atom 42)").unwrap();
    assert!(matches!(result, KlujurVal::Atom(_)));
}

#[test]
fn test_atom_with_nil() {
    let result = eval_str("(atom nil)").unwrap();
    assert!(matches!(result, KlujurVal::Atom(_)));
}

#[test]
fn test_atom_with_collection() {
    let result = eval_str("(atom [1 2 3])").unwrap();
    assert!(matches!(result, KlujurVal::Atom(_)));
}

#[test]
fn test_atom_with_map() {
    let result = eval_str("(atom {:a 1 :b 2})").unwrap();
    assert!(matches!(result, KlujurVal::Atom(_)));
}

// =============================================================================
// Deref (@)
// =============================================================================

#[test]
fn test_deref_atom() {
    assert_eval!("(deref (atom 42))", KlujurVal::int(42));
}

#[test]
fn test_deref_reader_macro() {
    assert_eval!("@(atom 42)", KlujurVal::int(42));
}

#[test]
fn test_deref_vector_atom() {
    assert_eval!(
        "@(atom [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_deref_nil_atom() {
    assert_eval!("@(atom nil)", KlujurVal::Nil);
}

// =============================================================================
// reset!
// =============================================================================

#[test]
fn test_reset_basic() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();

    let result = eval_str_with_env("(reset! a 42)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

#[test]
fn test_reset_returns_new_value() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    let result = eval_str_with_env("(reset! a :new-value)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));
}

#[test]
fn test_reset_multiple_times() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    eval_str_with_env("(reset! a 1)", &env).unwrap();
    eval_str_with_env("(reset! a 2)", &env).unwrap();
    eval_str_with_env("(reset! a 3)", &env).unwrap();

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));
}

// =============================================================================
// swap!
// =============================================================================

#[test]
fn test_swap_basic() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    let result = eval_str_with_env("(swap! a inc)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_swap_with_args() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    let result = eval_str_with_env("(swap! a + 10)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(10));
}

#[test]
fn test_swap_with_multiple_args() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    let result = eval_str_with_env("(swap! a + 1 2 3)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(6));
}

#[test]
fn test_swap_with_collection() {
    let env = new_env();
    eval_str_with_env("(def a (atom []))", &env).unwrap();

    eval_str_with_env("(swap! a conj 1)", &env).unwrap();
    eval_str_with_env("(swap! a conj 2)", &env).unwrap();
    eval_str_with_env("(swap! a conj 3)", &env).unwrap();

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_swap_with_map() {
    let env = new_env();
    eval_str_with_env("(def a (atom {}))", &env).unwrap();

    eval_str_with_env("(swap! a assoc :x 1)", &env).unwrap();
    eval_str_with_env("(swap! a assoc :y 2)", &env).unwrap();

    let result = eval_str_with_env("(get @a :x)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));

    let result = eval_str_with_env("(get @a :y)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}

#[test]
fn test_swap_returns_new_value() {
    let env = new_env();
    eval_str_with_env("(def a (atom 5))", &env).unwrap();

    let result = eval_str_with_env("(swap! a * 2)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(10));
}

#[test]
fn test_swap_with_anonymous_fn() {
    let env = new_env();
    eval_str_with_env("(def a (atom 5))", &env).unwrap();

    let result = eval_str_with_env("(swap! a (fn* [x] (* x x)))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(25));
}

// =============================================================================
// swap-vals!
// =============================================================================

#[test]
fn test_swap_vals_returns_both() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();

    let result = eval_str_with_env("(swap-vals! a inc)", &env).unwrap();
    // Returns [old-val new-val]
    assert_eq!(
        result,
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_swap_vals_with_args() {
    let env = new_env();
    eval_str_with_env("(def a (atom 10))", &env).unwrap();

    let result = eval_str_with_env("(swap-vals! a + 5)", &env).unwrap();
    assert_eq!(
        result,
        KlujurVal::vector(vec![KlujurVal::int(10), KlujurVal::int(15)])
    );
}

// =============================================================================
// reset-vals!
// =============================================================================

#[test]
fn test_reset_vals_returns_both() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();

    let result = eval_str_with_env("(reset-vals! a 42)", &env).unwrap();
    // Returns [old-val new-val]
    assert_eq!(
        result,
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(42)])
    );
}

// =============================================================================
// compare-and-set!
// =============================================================================

#[test]
fn test_compare_and_set_success() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();

    let result = eval_str_with_env("(compare-and-set! a 1 2)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}

#[test]
fn test_compare_and_set_failure() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();

    let result = eval_str_with_env("(compare-and-set! a 999 2)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));

    // Value should be unchanged
    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_compare_and_set_with_nil() {
    let env = new_env();
    eval_str_with_env("(def a (atom nil))", &env).unwrap();

    let result = eval_str_with_env("(compare-and-set! a nil :value)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    let result = eval_str_with_env("@a", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));
}

// =============================================================================
// atom?
// =============================================================================

#[test]
fn test_atom_predicate_true() {
    assert_eval!("(atom? (atom 1))", KlujurVal::bool(true));
}

#[test]
fn test_atom_predicate_false() {
    assert_eval!("(atom? 1)", KlujurVal::bool(false));
    assert_eval!("(atom? nil)", KlujurVal::bool(false));
    assert_eval!("(atom? [1 2])", KlujurVal::bool(false));
    assert_eval!("(atom? {:a 1})", KlujurVal::bool(false));
}

// =============================================================================
// Atoms in expressions
// =============================================================================

#[test]
fn test_atom_in_conditional() {
    let env = new_env();
    eval_str_with_env("(def counter (atom 0))", &env).unwrap();

    let result = eval_str_with_env("(if (< @counter 5) (swap! counter inc) :done)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_atom_in_loop() {
    let env = new_env();
    eval_str_with_env("(def counter (atom 0))", &env).unwrap();
    eval_str_with_env("(def result (atom []))", &env).unwrap();

    // Simulate a simple counting loop
    eval_str_with_env(
        "(do
           (swap! counter inc)
           (swap! result conj @counter)
           (swap! counter inc)
           (swap! result conj @counter)
           (swap! counter inc)
           (swap! result conj @counter))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("@result", &env).unwrap();
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Error cases
// =============================================================================

#[test]
fn test_swap_non_atom_error() {
    assert_eval_err!("(swap! 42 inc)");
}

#[test]
fn test_reset_non_atom_error() {
    assert_eval_err!("(reset! 42 1)");
}

#[test]
fn test_deref_non_derefable_error() {
    // Integers are not derefable
    assert_eval_err!("(deref 42)");
}

#[test]
fn test_compare_and_set_non_atom_error() {
    assert_eval_err!("(compare-and-set! 42 1 2)");
}

#[test]
fn test_swap_wrong_arity() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();

    // swap! needs at least 2 args (atom and function)
    let result = eval_str_with_env("(swap! a)", &env);
    assert!(result.is_err());
}

// =============================================================================
// Multiple atoms
// =============================================================================

#[test]
fn test_multiple_atoms_independent() {
    let env = new_env();
    eval_str_with_env("(def a (atom 0))", &env).unwrap();
    eval_str_with_env("(def b (atom 100))", &env).unwrap();

    eval_str_with_env("(swap! a inc)", &env).unwrap();
    eval_str_with_env("(swap! b dec)", &env).unwrap();

    let result_a = eval_str_with_env("@a", &env).unwrap();
    let result_b = eval_str_with_env("@b", &env).unwrap();

    assert_eq!(result_a, KlujurVal::int(1));
    assert_eq!(result_b, KlujurVal::int(99));
}

#[test]
fn test_atom_stored_in_collection() {
    let env = new_env();
    eval_str_with_env("(def a (atom 1))", &env).unwrap();
    eval_str_with_env("(def v [a])", &env).unwrap();

    // Can retrieve and deref atom from vector
    let result = eval_str_with_env("@(first v)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));

    // Modifying through retrieved reference
    eval_str_with_env("(swap! (first v) inc)", &env).unwrap();

    let result = eval_str_with_env("@a", &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}
