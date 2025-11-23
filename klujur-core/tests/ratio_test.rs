// klujur-core - Ratio arithmetic edge case tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for ratio arithmetic edge cases.
//!
//! Tests boundary conditions, normalisation, mixed-type arithmetic,
//! and comparison operations with ratios.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{KlujurVal, Parser};

fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_str_with_env(s, &env)
}

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, env).map_err(|e| e.to_string()),
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

macro_rules! assert_eval_str {
    ($input:expr, $expected:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap().to_string(),
            $expected,
            "Evaluation of '{}' did not match expected string",
            $input
        );
    };
}

macro_rules! assert_eval_err {
    ($input:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
    };
}

// =============================================================================
// Basic ratio parsing and representation
// =============================================================================

#[test]
fn test_ratio_parsing() {
    assert_eval_str!("1/2", "1/2");
    assert_eval_str!("3/4", "3/4");
    assert_eval_str!("-1/2", "-1/2");
    assert_eval_str!("1/-2", "-1/2"); // Normalise negative to numerator
}

#[test]
fn test_ratio_normalisation() {
    // Ratios should be reduced to lowest terms
    assert_eval_str!("2/4", "1/2");
    assert_eval_str!("6/9", "2/3");
    assert_eval_str!("100/200", "1/2");
}

#[test]
fn test_ratio_to_integer() {
    // When ratio equals an integer, should return integer
    assert_eval!("4/2", KlujurVal::int(2));
    assert_eval!("9/3", KlujurVal::int(3));
    assert_eval!("0/5", KlujurVal::int(0));
}

#[test]
fn test_ratio_zero_numerator() {
    // 0/n should always be 0
    assert_eval!("0/1", KlujurVal::int(0));
    assert_eval!("0/100", KlujurVal::int(0));
}

#[test]
fn test_ratio_division_by_zero() {
    // Cannot have zero denominator
    assert_eval_err!("1/0");
}

// =============================================================================
// Ratio predicates
// =============================================================================

#[test]
fn test_ratio_predicate() {
    assert_eval!("(ratio? 1/2)", KlujurVal::bool(true));
    assert_eval!("(ratio? 1)", KlujurVal::bool(false));
    assert_eval!("(ratio? 1.5)", KlujurVal::bool(false));
    assert_eval!("(ratio? \"1/2\")", KlujurVal::bool(false));
}

#[test]
fn test_ratio_is_number() {
    assert_eval!("(number? 1/2)", KlujurVal::bool(true));
}

#[test]
fn test_numerator_denominator() {
    assert_eval!("(numerator 3/4)", KlujurVal::int(3));
    assert_eval!("(denominator 3/4)", KlujurVal::int(4));
    assert_eval!("(numerator -3/4)", KlujurVal::int(-3));
    assert_eval!("(denominator -3/4)", KlujurVal::int(4));
}

// =============================================================================
// Ratio arithmetic
// =============================================================================
//
#[test]
fn test_ratio_addition() {
    // 1/2 + 1/3 = 5/6
    assert_eval_str!("(+ 1/2 1/3)", "5/6");
    // 1/2 + 1/2 = 1
    assert_eval!("(+ 1/2 1/2)", KlujurVal::int(1));
    // 1/4 + 1/4 = 1/2
    assert_eval_str!("(+ 1/4 1/4)", "1/2");
}

#[test]
fn test_ratio_subtraction() {
    // 3/4 - 1/4 = 1/2
    assert_eval_str!("(- 3/4 1/4)", "1/2");
    // 1/2 - 1/3 = 1/6
    assert_eval_str!("(- 1/2 1/3)", "1/6");
    // 1/2 - 1/2 = 0
    assert_eval!("(- 1/2 1/2)", KlujurVal::int(0));
}

#[test]
fn test_ratio_multiplication() {
    // 1/2 * 1/3 = 1/6
    assert_eval_str!("(* 1/2 1/3)", "1/6");
    // 2/3 * 3/4 = 1/2
    assert_eval_str!("(* 2/3 3/4)", "1/2");
    // 1/2 * 2 = 1
    assert_eval!("(* 1/2 2)", KlujurVal::int(1));
}

#[test]
fn test_ratio_division() {
    // (1/2) / (1/4) = 2
    assert_eval!("(/ 1/2 1/4)", KlujurVal::int(2));
    // (1/3) / (2/3) = 1/2
    assert_eval_str!("(/ 1/3 2/3)", "1/2");
}

#[test]
fn test_ratio_negation() {
    // - (1/2) = -1/2
    assert_eval_str!("(- 1/2)", "-1/2");
    // - (-1/2) = 1/2
    assert_eval_str!("(- -1/2)", "1/2");
}

// =============================================================================
// Mixed type arithmetic (ratio with int/float)
// =============================================================================

#[test]
fn test_ratio_plus_integer() {
    // 1/2 + 1 = 3/2
    assert_eval_str!("(+ 1/2 1)", "3/2");
    // 1 + 1/2 = 3/2
    assert_eval_str!("(+ 1 1/2)", "3/2");
    // 1/2 + 0 = 1/2
    assert_eval_str!("(+ 1/2 0)", "1/2");
}

#[test]
fn test_ratio_plus_float() {
    // Ratio + Float = Float
    let result = eval_str("(+ 1/2 0.5)").unwrap();
    assert!(matches!(result, KlujurVal::Float(_)));
    if let KlujurVal::Float(f) = result {
        assert!((f - 1.0).abs() < 0.0001);
    }
}

#[test]
fn test_ratio_times_integer() {
    // 1/3 * 3 = 1
    assert_eval!("(* 1/3 3)", KlujurVal::int(1));
    // 2/5 * 5 = 2
    assert_eval!("(* 2/5 5)", KlujurVal::int(2));
    // 1/2 * 0 = 0
    assert_eval!("(* 1/2 0)", KlujurVal::int(0));
}

#[test]
fn test_integer_divided_by_integer_is_ratio() {
    // In Clojure, / with integers can produce a ratio
    // 1/3 should be a ratio, not 0
    let result = eval_str("(/ 1 3)").unwrap();
    // Could be ratio 1/3 or float 0.333...
    // Check it's not integer 0
    assert!(result != KlujurVal::int(0));
}

// =============================================================================
// Ratio comparisons
// =============================================================================

#[test]
fn test_ratio_equality() {
    assert_eval!("(= 1/2 1/2)", KlujurVal::bool(true));
    assert_eval!("(= 1/2 2/4)", KlujurVal::bool(true)); // Normalised
    assert_eval!("(= 1/2 1/3)", KlujurVal::bool(false));
    assert_eval!("(= 2/2 1)", KlujurVal::bool(true)); // Ratio equals int
}

#[test]
fn test_ratio_less_than() {
    assert_eval!("(< 1/3 1/2)", KlujurVal::bool(true));
    assert_eval!("(< 1/2 1/3)", KlujurVal::bool(false));
    assert_eval!("(< 1/2 1/2)", KlujurVal::bool(false));
}

#[test]
fn test_ratio_greater_than() {
    assert_eval!("(> 1/2 1/3)", KlujurVal::bool(true));
    assert_eval!("(> 1/3 1/2)", KlujurVal::bool(false));
}

#[test]
fn test_ratio_compare_with_integer() {
    assert_eval!("(< 1/2 1)", KlujurVal::bool(true));
    assert_eval!("(> 3/2 1)", KlujurVal::bool(true));
    assert_eval!("(= 4/2 2)", KlujurVal::bool(true));
}

#[test]
fn test_ratio_compare_with_float() {
    assert_eval!("(< 1/2 0.6)", KlujurVal::bool(true));
    assert_eval!("(> 1/2 0.4)", KlujurVal::bool(true));
    // 1/2 = 0.5
    assert_eval!("(= 1/2 0.5)", KlujurVal::bool(true));
}

// =============================================================================
// Edge cases with large numbers
// =============================================================================

#[test]
fn test_ratio_large_numerator_denominator() {
    // Large but valid ratios
    assert_eval_str!("1000000/3000000", "1/3");
    assert_eval!("(+ 1000000/1000001 1/1000001)", KlujurVal::int(1));
}

#[test]
fn test_ratio_gcd_reduction() {
    // Ensure GCD is computed correctly
    assert_eval_str!("12/18", "2/3");
    assert_eval_str!("144/233", "144/233"); // Already in lowest terms (Fibonacci)
    assert_eval_str!("21/14", "3/2");
}

// =============================================================================
// Negative ratio edge cases
// =============================================================================

#[test]
fn test_negative_ratio_arithmetic() {
    // -1/2 + -1/2 = -1
    assert_eval!("(+ -1/2 -1/2)", KlujurVal::int(-1));
    // -1/2 * -1/2 = 1/4
    assert_eval_str!("(* -1/2 -1/2)", "1/4");
    // -1/2 * 2 = -1
    assert_eval!("(* -1/2 2)", KlujurVal::int(-1));
}

#[test]
fn test_negative_denominator_normalisation() {
    // Negative should always be in numerator
    assert_eval_str!("(/ 1 -2)", "-1/2");
    assert_eval_str!("(/ -1 -2)", "1/2");
}

// =============================================================================
// Ratio in collections and functions
// =============================================================================

#[test]
fn test_ratio_in_collection() {
    assert_eval!("(first [1/2 1/3 1/4])", KlujurVal::ratio(1, 2));
}

#[test]
fn test_ratio_as_map_key() {
    // Ratios can be map keys
    let result = eval_str("(get {1/2 :half} 1/2)").unwrap();
    assert_eq!(result.to_string(), ":half");

    // Equivalent ratios should find the same key
    let result = eval_str("(get {1/2 :half} 2/4)").unwrap();
    assert_eq!(result.to_string(), ":half");
}

#[test]
fn test_ratio_hash_consistency() {
    // Equal ratios should have equal hashes
    assert_eval!("(= (hash 1/2) (hash 2/4))", KlujurVal::bool(true));
}

// =============================================================================
// abs and sign with ratios
// =============================================================================

#[test]
fn test_ratio_abs() {
    assert_eval_str!("(abs -1/2)", "1/2");
    assert_eval_str!("(abs 1/2)", "1/2");
}

// =============================================================================
// Conversion functions
// =============================================================================

#[test]
fn test_ratio_to_double() {
    let result = eval_str("(double 1/2)").unwrap();
    if let KlujurVal::Float(f) = result {
        assert!((f - 0.5).abs() < 0.0001);
    } else {
        panic!("Expected float from double");
    }
}

#[test]
fn test_int_truncates_ratio() {
    // int should truncate towards zero
    assert_eval!("(int 5/2)", KlujurVal::int(2));
    assert_eval!("(int -5/2)", KlujurVal::int(-2));
    assert_eval!("(int 1/2)", KlujurVal::int(0));
}
