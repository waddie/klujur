// klujur-core - Logic integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur logic and truthiness.

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

macro_rules! assert_eval {
    ($input:expr, $expected:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

// =============================================================================
// Truthiness Fundamentals
// =============================================================================
// In Clojure, only nil and false are falsy. Everything else is truthy.

#[test]
fn test_nil_is_falsy() {
    assert_eval!(
        "(if nil :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("falsy"))
    );
    assert_eval!("(boolean nil)", KlujurVal::bool(false));
}

#[test]
fn test_false_is_falsy() {
    assert_eval!(
        "(if false :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("falsy"))
    );
    assert_eval!("(boolean false)", KlujurVal::bool(false));
}

#[test]
fn test_true_is_truthy() {
    assert_eval!(
        "(if true :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!("(boolean true)", KlujurVal::bool(true));
}

#[test]
fn test_numbers_are_truthy() {
    // Including zero!
    assert_eval!(
        "(if 0 :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if 1 :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if -1 :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if 0.0 :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

#[test]
fn test_strings_are_truthy() {
    // Including empty string!
    assert_eval!(
        "(if \"\" :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if \"hello\" :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

#[test]
fn test_collections_are_truthy() {
    // Including empty collections!
    assert_eval!(
        "(if '() :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if [] :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if {} :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if #{} :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

#[test]
fn test_keywords_and_symbols_are_truthy() {
    assert_eval!(
        "(if :keyword :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if 'symbol :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

// =============================================================================
// boolean
// =============================================================================

#[test]
fn test_boolean_coercion() {
    assert_eval!("(boolean true)", KlujurVal::bool(true));
    assert_eval!("(boolean false)", KlujurVal::bool(false));
    assert_eval!("(boolean nil)", KlujurVal::bool(false));
    assert_eval!("(boolean 0)", KlujurVal::bool(true));
    assert_eval!("(boolean \"\")", KlujurVal::bool(true));
    assert_eval!("(boolean [])", KlujurVal::bool(true));
    assert_eval!("(boolean :keyword)", KlujurVal::bool(true));
}

// =============================================================================
// not
// =============================================================================

#[test]
fn test_not_with_truthy_values() {
    assert_eval!("(not true)", KlujurVal::bool(false));
    assert_eval!("(not 1)", KlujurVal::bool(false));
    assert_eval!("(not 0)", KlujurVal::bool(false)); // 0 is truthy!
    assert_eval!("(not \"\")", KlujurVal::bool(false)); // empty string is truthy!
    assert_eval!("(not [])", KlujurVal::bool(false)); // empty vector is truthy!
    assert_eval!("(not '())", KlujurVal::bool(false)); // empty list is truthy!
    assert_eval!("(not {})", KlujurVal::bool(false)); // empty map is truthy!
    assert_eval!("(not #{})", KlujurVal::bool(false)); // empty set is truthy!
    assert_eval!("(not :keyword)", KlujurVal::bool(false));
}

#[test]
fn test_not_with_falsy_values() {
    assert_eval!("(not nil)", KlujurVal::bool(true));
    assert_eval!("(not false)", KlujurVal::bool(true));
}

#[test]
fn test_double_negation() {
    assert_eval!("(not (not nil))", KlujurVal::bool(false));
    assert_eval!("(not (not false))", KlujurVal::bool(false));
    assert_eval!("(not (not true))", KlujurVal::bool(true));
    assert_eval!("(not (not 0))", KlujurVal::bool(true));
    assert_eval!("(not (not []))", KlujurVal::bool(true));
}

// =============================================================================
// Predicates
// =============================================================================

#[test]
fn test_nil_predicate() {
    assert_eval!("(nil? nil)", KlujurVal::bool(true));
    assert_eval!("(nil? false)", KlujurVal::bool(false));
    assert_eval!("(nil? 0)", KlujurVal::bool(false));
    assert_eval!("(nil? \"\")", KlujurVal::bool(false));
    assert_eval!("(nil? [])", KlujurVal::bool(false));
}

#[test]
fn test_some_predicate() {
    // some? is the opposite of nil?
    assert_eval!("(some? nil)", KlujurVal::bool(false));
    assert_eval!("(some? false)", KlujurVal::bool(true)); // false is NOT nil
    assert_eval!("(some? 0)", KlujurVal::bool(true));
    assert_eval!("(some? \"\")", KlujurVal::bool(true));
    assert_eval!("(some? [])", KlujurVal::bool(true));
}

// =============================================================================
// Equality with nil and false
// =============================================================================

#[test]
fn test_equality_with_nil() {
    assert_eval!("(= nil nil)", KlujurVal::bool(true));
    assert_eval!("(= nil false)", KlujurVal::bool(false));
    assert_eval!("(= nil 0)", KlujurVal::bool(false));
}

#[test]
fn test_equality_with_false() {
    assert_eval!("(= false false)", KlujurVal::bool(true));
    assert_eval!("(= false nil)", KlujurVal::bool(false));
    assert_eval!("(= false 0)", KlujurVal::bool(false));
}

#[test]
fn test_equality_with_collections() {
    assert_eval!("(= [] [])", KlujurVal::bool(true));
    assert_eval!("(= {} {})", KlujurVal::bool(true));
    assert_eval!("(= #{} #{})", KlujurVal::bool(true));
}

// =============================================================================
// Empty Sequences and Truthiness
// =============================================================================

#[test]
fn test_empty_seq_truthiness() {
    // Empty sequences are truthy - this is a common gotcha!
    assert_eval!(
        "(if '() :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
    assert_eval!(
        "(if [] :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

// =============================================================================
// Type Predicates
// =============================================================================

#[test]
fn test_boolean_predicate() {
    assert_eval!("(boolean? true)", KlujurVal::bool(true));
    assert_eval!("(boolean? false)", KlujurVal::bool(true));
    assert_eval!("(boolean? nil)", KlujurVal::bool(false));
    assert_eval!("(boolean? 1)", KlujurVal::bool(false));
}

#[test]
fn test_fn_predicate() {
    assert_eval!("(fn? (fn* [] 1))", KlujurVal::bool(true));
    assert_eval!("(fn? +)", KlujurVal::bool(true));
    assert_eval!("(fn? 1)", KlujurVal::bool(false));
    assert_eval!("(fn? nil)", KlujurVal::bool(false));
}
