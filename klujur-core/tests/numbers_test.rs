// klujur-core - Numbers integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur numeric operations.

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
// Basic Arithmetic
// =============================================================================

#[test]
fn test_addition() {
    assert_eval!("(+)", KlujurVal::int(0)); // identity
    assert_eval!("(+ 1)", KlujurVal::int(1));
    assert_eval!("(+ 1 2)", KlujurVal::int(3));
    assert_eval!("(+ 1 2 3 4)", KlujurVal::int(10));
    assert_eval!("(+ 2.5 3.0)", KlujurVal::float(5.5));
}

#[test]
fn test_subtraction() {
    assert_eval!("(- 1)", KlujurVal::int(-1)); // negation
    assert_eval!("(- 3 2)", KlujurVal::int(1));
    assert_eval!("(- 1 2 3)", KlujurVal::int(-4));
    assert_eval!("(- 5.0 2.5)", KlujurVal::float(2.5));
}

#[test]
fn test_multiplication() {
    assert_eval!("(*)", KlujurVal::int(1)); // identity
    assert_eval!("(* 5)", KlujurVal::int(5));
    assert_eval!("(* 2 3)", KlujurVal::int(6));
    assert_eval!("(* 1 2 3 4)", KlujurVal::int(24));
    assert_eval!("(* 2.5 3.0)", KlujurVal::float(7.5));
}

#[test]
fn test_division() {
    assert_eval!("(/ 2)", KlujurVal::float(0.5)); // reciprocal
    assert_eval!("(/ 6 3)", KlujurVal::float(2.0));
    assert_eval!("(/ 12 3 2)", KlujurVal::float(2.0));
    assert_eval!("(/ 5.0 2.0)", KlujurVal::float(2.5));
}

#[test]
fn test_division_by_zero() {
    assert_eval_err!("(/ 1 0)");
}

// =============================================================================
// Integer Division and Modulo
// =============================================================================

#[test]
fn test_quot() {
    assert_eval!("(quot 10 3)", KlujurVal::int(3));
    assert_eval!("(quot -10 3)", KlujurVal::int(-3));
    assert_eval!("(quot 10 -3)", KlujurVal::int(-3));
    assert_eval!("(quot -10 -3)", KlujurVal::int(3));
}

#[test]
fn test_rem() {
    assert_eval!("(rem 10 3)", KlujurVal::int(1));
    assert_eval!("(rem -10 3)", KlujurVal::int(-1)); // sign follows dividend
    assert_eval!("(rem 10 -3)", KlujurVal::int(1));
    assert_eval!("(rem -10 -3)", KlujurVal::int(-1));
}

#[test]
fn test_mod() {
    assert_eval!("(mod 10 3)", KlujurVal::int(1));
    assert_eval!("(mod -10 3)", KlujurVal::int(2)); // sign follows divisor
    assert_eval!("(mod 10 -3)", KlujurVal::int(-2));
    assert_eval!("(mod -10 -3)", KlujurVal::int(-1));
}

// =============================================================================
// Comparisons
// =============================================================================

#[test]
fn test_equality() {
    assert_eval!("(= 1 1)", KlujurVal::bool(true));
    assert_eval!("(= 1 1 1 1)", KlujurVal::bool(true));
    assert_eval!("(= 1 2)", KlujurVal::bool(false));
    assert_eval!("(= 1 1 2)", KlujurVal::bool(false));
    assert_eval!("(= 1.0 1.0)", KlujurVal::bool(true));
    assert_eval!("(=)", KlujurVal::bool(true)); // vacuous truth
}

#[test]
fn test_not_equal() {
    assert_eval!("(not= 1 2)", KlujurVal::bool(true));
    assert_eval!("(not= 1 1)", KlujurVal::bool(false));
    assert_eval!("(not= 1 2 3)", KlujurVal::bool(true));
    assert_eval!("(not= 1 1 1)", KlujurVal::bool(false));
}

#[test]
fn test_less_than() {
    assert_eval!("(< 1 2)", KlujurVal::bool(true));
    assert_eval!("(< 2 1)", KlujurVal::bool(false));
    assert_eval!("(< 1 1)", KlujurVal::bool(false));
    assert_eval!("(< 1 2 3 4)", KlujurVal::bool(true));
    assert_eval!("(< 1 2 2 3)", KlujurVal::bool(false)); // not strictly increasing
    assert_eval!("(<)", KlujurVal::bool(true)); // vacuous truth
}

#[test]
fn test_less_than_or_equal() {
    assert_eval!("(<= 1 2)", KlujurVal::bool(true));
    assert_eval!("(<= 1 1)", KlujurVal::bool(true));
    assert_eval!("(<= 2 1)", KlujurVal::bool(false));
    assert_eval!("(<= 1 2 2 3)", KlujurVal::bool(true));
    assert_eval!("(<= 1 3 2)", KlujurVal::bool(false));
}

#[test]
fn test_greater_than() {
    assert_eval!("(> 2 1)", KlujurVal::bool(true));
    assert_eval!("(> 1 2)", KlujurVal::bool(false));
    assert_eval!("(> 1 1)", KlujurVal::bool(false));
    assert_eval!("(> 4 3 2 1)", KlujurVal::bool(true));
    assert_eval!("(> 4 3 3 1)", KlujurVal::bool(false));
}

#[test]
fn test_greater_than_or_equal() {
    assert_eval!("(>= 2 1)", KlujurVal::bool(true));
    assert_eval!("(>= 1 1)", KlujurVal::bool(true));
    assert_eval!("(>= 1 2)", KlujurVal::bool(false));
    assert_eval!("(>= 4 3 3 1)", KlujurVal::bool(true));
}

// =============================================================================
// Numeric Predicates
// =============================================================================

#[test]
fn test_number_predicate() {
    assert_eval!("(number? 1)", KlujurVal::bool(true));
    assert_eval!("(number? 1.5)", KlujurVal::bool(true));
    assert_eval!("(number? 1/2)", KlujurVal::bool(true));
    assert_eval!("(number? \"1\")", KlujurVal::bool(false));
    assert_eval!("(number? nil)", KlujurVal::bool(false));
}

#[test]
fn test_integer_predicate() {
    assert_eval!("(integer? 1)", KlujurVal::bool(true));
    assert_eval!("(integer? -5)", KlujurVal::bool(true));
    assert_eval!("(integer? 1.0)", KlujurVal::bool(false));
    assert_eval!("(integer? 1/2)", KlujurVal::bool(false));
}

#[test]
fn test_float_predicate() {
    assert_eval!("(float? 1.0)", KlujurVal::bool(true));
    assert_eval!("(float? 1.5)", KlujurVal::bool(true));
    assert_eval!("(float? 1)", KlujurVal::bool(false));
    assert_eval!("(float? 1/2)", KlujurVal::bool(false));
}

// =============================================================================
// Mixed Integer/Float Operations
// =============================================================================

#[test]
fn test_mixed_arithmetic() {
    // Int + Float = Float
    assert_eval!("(+ 1 2.0)", KlujurVal::float(3.0));
    assert_eval!("(+ 1.0 2)", KlujurVal::float(3.0));
    assert_eval!("(* 2 3.0)", KlujurVal::float(6.0));
    assert_eval!("(- 5.0 2)", KlujurVal::float(3.0));
}

#[test]
fn test_comparison_mixed_types() {
    // Int and Float can be compared
    assert_eval!("(< 1 2.0)", KlujurVal::bool(true));
    assert_eval!("(> 2.0 1)", KlujurVal::bool(true));
    assert_eval!("(<= 1.0 1)", KlujurVal::bool(true));
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_large_numbers() {
    assert_eval!("(+ 1000000000 1000000000)", KlujurVal::int(2000000000));
    assert_eval!("(* 1000000 1000000)", KlujurVal::int(1000000000000));
}

#[test]
fn test_negative_operations() {
    assert_eval!("(+ -1 -2)", KlujurVal::int(-3));
    assert_eval!("(* -2 -3)", KlujurVal::int(6));
    assert_eval!("(- -5)", KlujurVal::int(5));
}
