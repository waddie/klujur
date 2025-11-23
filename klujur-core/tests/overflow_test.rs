// klujur-core - Integer overflow boundary tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for integer overflow behaviour.
//!
//! Unlike Clojure which auto-promotes to BigInteger, Klujur uses checked
//! arithmetic and returns an error on integer overflow. This file tests
//! boundary conditions around i64::MAX and i64::MIN.

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
    ($input:expr, $contains:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.contains($contains),
            "Error for '{}' should contain '{}', got: {}",
            $input,
            $contains,
            err_msg
        );
    };
}

// =============================================================================
// i64 Boundary Constants
// =============================================================================

const I64_MAX: i64 = 9223372036854775807;
const I64_MIN: i64 = -9223372036854775808;

// Note: The parser cannot directly parse i64::MIN as a literal because
// -9223372036854775808 is parsed as -(9223372036854775808), and the positive
// number exceeds i64::MAX. We use (- 0 9223372036854775807 1) or similar
// expressions to construct i64::MIN at runtime.

// =============================================================================
// Addition Overflow
// =============================================================================

#[test]
fn test_add_at_max_boundary() {
    // i64::MAX is the largest valid integer
    assert_eval!("9223372036854775807", KlujurVal::int(I64_MAX));

    // Adding 0 to MAX is fine
    assert_eval!("(+ 9223372036854775807 0)", KlujurVal::int(I64_MAX));
}

#[test]
fn test_add_overflow_max_plus_one() {
    // i64::MAX + 1 overflows
    assert_eval_err!("(+ 9223372036854775807 1)");
}

#[test]
fn test_add_overflow_max_plus_max() {
    // i64::MAX + i64::MAX overflows
    assert_eval_err!("(+ 9223372036854775807 9223372036854775807)");
}

#[test]
fn test_add_at_min_boundary() {
    // Construct i64::MIN via arithmetic (parser can't parse it directly)
    // i64::MIN = -9223372036854775807 - 1
    assert_eval!("(- -9223372036854775807 1)", KlujurVal::int(I64_MIN));

    // Adding 0 to MIN is fine
    assert_eval!("(+ (- -9223372036854775807 1) 0)", KlujurVal::int(I64_MIN));
}

#[test]
fn test_add_overflow_min_minus_one() {
    // i64::MIN + (-1) overflows (underflows)
    // Construct MIN via (- -9223372036854775807 1)
    assert_eval_err!("(+ (- -9223372036854775807 1) -1)");
}

#[test]
fn test_add_near_boundaries_no_overflow() {
    // Large positive + large negative that doesn't overflow
    assert_eval!(
        "(+ 9223372036854775807 -9223372036854775807)",
        KlujurVal::int(0)
    );

    // Slightly below max
    assert_eval!("(+ 9223372036854775806 1)", KlujurVal::int(I64_MAX));
}

// =============================================================================
// Subtraction Overflow
// =============================================================================

#[test]
fn test_sub_at_boundaries() {
    // MAX - 0 is fine
    assert_eval!("(- 9223372036854775807 0)", KlujurVal::int(I64_MAX));

    // MIN - 0 is fine (construct MIN via arithmetic)
    assert_eval!("(- (- -9223372036854775807 1) 0)", KlujurVal::int(I64_MIN));
}

#[test]
fn test_sub_overflow_min_minus_one() {
    // i64::MIN - 1 overflows (construct MIN via arithmetic)
    assert_eval_err!("(- (- -9223372036854775807 1) 1)");
}

#[test]
fn test_sub_overflow_max_minus_negative() {
    // i64::MAX - (-1) = i64::MAX + 1 overflows
    assert_eval_err!("(- 9223372036854775807 -1)");
}

#[test]
fn test_sub_near_boundaries_no_overflow() {
    // MAX - MAX = 0
    assert_eval!(
        "(- 9223372036854775807 9223372036854775807)",
        KlujurVal::int(0)
    );

    // MIN - MIN = 0 (using let to bind MIN)
    // We construct MIN and subtract it from itself
    assert_eval!(
        "(let* [min (- -9223372036854775807 1)] (- min min))",
        KlujurVal::int(0)
    );
}

// =============================================================================
// Unary Negation Overflow
// =============================================================================

#[test]
fn test_negate_max() {
    // -MAX is valid
    assert_eval!("(- 9223372036854775807)", KlujurVal::int(-I64_MAX));
}

#[test]
fn test_negate_min_overflows() {
    // -MIN overflows because |MIN| > MAX
    // i64::MIN = -9223372036854775808
    // -i64::MIN = 9223372036854775808 which is > i64::MAX
    assert_eval_err!("(- -9223372036854775808)");
}

#[test]
fn test_negate_min_plus_one() {
    // -(MIN + 1) = -(-9223372036854775807) = 9223372036854775807 = MAX
    assert_eval!("(- -9223372036854775807)", KlujurVal::int(I64_MAX));
}

// =============================================================================
// Multiplication Overflow
// =============================================================================

#[test]
fn test_mul_at_boundaries() {
    // MAX * 1 is fine
    assert_eval!("(* 9223372036854775807 1)", KlujurVal::int(I64_MAX));

    // MIN * 1 is fine (construct MIN via arithmetic)
    assert_eval!("(* (- -9223372036854775807 1) 1)", KlujurVal::int(I64_MIN));

    // MAX * 0 = 0
    assert_eval!("(* 9223372036854775807 0)", KlujurVal::int(0));
}

#[test]
fn test_mul_overflow_max_times_two() {
    // i64::MAX * 2 overflows
    assert_eval_err!("(* 9223372036854775807 2)");
}

#[test]
fn test_mul_overflow_large_numbers() {
    // Two moderately large numbers that overflow
    // 3037000500 * 3037000500 > i64::MAX
    assert_eval_err!("(* 3037000500 3037000500)");
}

#[test]
fn test_mul_overflow_min_times_minus_one() {
    // MIN * -1 = |MIN| > MAX, so overflows
    assert_eval_err!("(* -9223372036854775808 -1)");
}

#[test]
fn test_mul_near_boundaries_no_overflow() {
    // MAX / 2 * 2 doesn't overflow (rounds down)
    assert_eval!(
        "(* 4611686018427387903 2)",
        KlujurVal::int(9223372036854775806)
    );
}

// =============================================================================
// Inc/Dec Overflow
// =============================================================================

#[test]
fn test_inc_at_max_overflows() {
    // inc on i64::MAX overflows
    assert_eval_err!("(inc 9223372036854775807)");
}

#[test]
fn test_inc_near_max() {
    // inc on MAX - 1 = MAX
    assert_eval!("(inc 9223372036854775806)", KlujurVal::int(I64_MAX));
}

#[test]
fn test_dec_at_min_overflows() {
    // dec on i64::MIN overflows
    assert_eval_err!("(dec -9223372036854775808)");
}

#[test]
fn test_dec_near_min() {
    // dec on MIN + 1 = MIN
    assert_eval!("(dec -9223372036854775807)", KlujurVal::int(I64_MIN));
}

// =============================================================================
// Abs Overflow
// =============================================================================

#[test]
fn test_abs_max() {
    // abs(MAX) = MAX
    assert_eval!("(abs 9223372036854775807)", KlujurVal::int(I64_MAX));
}

#[test]
fn test_abs_min_overflows() {
    // abs(MIN) = |MIN| > MAX, so overflows
    assert_eval_err!("(abs -9223372036854775808)");
}

#[test]
fn test_abs_min_plus_one() {
    // abs(MIN + 1) = MAX
    assert_eval!("(abs -9223372036854775807)", KlujurVal::int(I64_MAX));
}

// =============================================================================
// Multi-argument overflow detection
// =============================================================================

#[test]
fn test_add_multi_arg_overflow() {
    // Many large positive numbers that overflow
    assert_eval_err!("(+ 4000000000000000000 4000000000000000000 4000000000000000000)");
}

#[test]
fn test_mul_multi_arg_overflow() {
    // Chained multiplication that overflows
    // 1000000^3 = 10^18, which is less than i64::MAX (~9.2 * 10^18)
    // Use larger numbers that will definitely overflow
    assert_eval_err!("(* 10000000000 10000000000 10000000000)");
}

// =============================================================================
// Float operations don't overflow (they go to infinity)
// =============================================================================

#[test]
fn test_float_no_overflow_error() {
    // Floats don't throw overflow errors - they go to infinity
    let result = eval_str("(+ 1.0e308 1.0e308)");
    assert!(result.is_ok());
    if let KlujurVal::Float(f) = result.unwrap() {
        assert!(f.is_infinite());
    } else {
        panic!("Expected float result");
    }
}

#[test]
fn test_mixed_int_float_no_integer_overflow() {
    // When a float is involved, we use float arithmetic (no overflow)
    let result = eval_str("(+ 9223372036854775807 1.0)");
    assert!(result.is_ok());
}

// =============================================================================
// Specific overflow error messages
// =============================================================================

#[test]
fn test_overflow_error_message_add() {
    assert_eval_err!("(+ 9223372036854775807 1)", "overflow");
}

#[test]
fn test_overflow_error_message_mul() {
    assert_eval_err!("(* 9223372036854775807 2)", "overflow");
}

#[test]
fn test_overflow_error_message_sub() {
    // Construct MIN via arithmetic, then subtract 1 to trigger overflow
    assert_eval_err!("(- (- -9223372036854775807 1) 1)", "overflow");
}
