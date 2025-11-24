// klujur-core - BigInt integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for BigInt and BigRatio support.
//!
//! Tests for:
//! - BigInt literal parsing and auto-promotion
//! - Auto-promoting operators: +', -', *', inc', dec'
//! - Arithmetic with BigInt operands
//! - Comparison operators with BigInt
//! - Predicates: bigint?, integer?, number?

mod common;

use common::{KlujurVal, eval_str};

// =============================================================================
// Literal parsing and auto-promotion
// =============================================================================

#[test]
fn test_bigint_literal_auto_promotion() {
    // i64::MAX stays as Int
    let result = eval_str("9223372036854775807").unwrap();
    assert!(matches!(result, KlujurVal::Int(_)));

    // i64::MAX + 1 becomes BigInt
    let result = eval_str("9223372036854775808").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "9223372036854775808N");
}

#[test]
fn test_bigint_negative_literal() {
    // i64::MIN stays as Int
    let result = eval_str("-9223372036854775808").unwrap();
    assert!(matches!(result, KlujurVal::Int(_)));

    // i64::MIN - 1 becomes BigInt
    let result = eval_str("-9223372036854775809").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
}

#[test]
fn test_bigint_display_format() {
    let result = eval_str("9223372036854775808").unwrap();
    assert!(result.to_string().ends_with("N"));
}

// =============================================================================
// Auto-promoting operators
// =============================================================================

#[test]
fn test_add_prime_basic() {
    let result = eval_str("(+' 1 2)").unwrap();
    assert_eq!(result, KlujurVal::int(3));
}

#[test]
fn test_add_prime_promotes_on_overflow() {
    // i64::MAX + 1 would overflow, but +' promotes
    let result = eval_str("(+' 9223372036854775807 1)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "9223372036854775808N");
}

#[test]
fn test_sub_prime_promotes_on_overflow() {
    // i64::MIN - 1 would overflow, but -' promotes
    let result = eval_str("(-' -9223372036854775808 1)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
}

#[test]
fn test_mul_prime_promotes_on_overflow() {
    // Large multiplication that would overflow
    let result = eval_str("(*' 9223372036854775807 2)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "18446744073709551614N");
}

#[test]
fn test_inc_prime_promotes_on_overflow() {
    // inc' on i64::MAX
    let result = eval_str("(inc' 9223372036854775807)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "9223372036854775808N");
}

#[test]
fn test_dec_prime_promotes_on_overflow() {
    // dec' on i64::MIN
    let result = eval_str("(dec' -9223372036854775808)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
}

// =============================================================================
// Standard ops error on overflow
// =============================================================================

#[test]
fn test_add_errors_on_overflow() {
    let result = eval_str("(+ 9223372036854775807 1)");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("overflow"));
}

#[test]
fn test_sub_errors_on_overflow() {
    let result = eval_str("(- -9223372036854775808 1)");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("overflow"));
}

#[test]
fn test_mul_errors_on_overflow() {
    let result = eval_str("(* 9223372036854775807 2)");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("overflow"));
}

#[test]
fn test_inc_errors_on_overflow() {
    let result = eval_str("(inc 9223372036854775807)");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("overflow"));
}

#[test]
fn test_dec_errors_on_overflow() {
    let result = eval_str("(dec -9223372036854775808)");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("overflow"));
}

// =============================================================================
// BigInt arithmetic
// =============================================================================

#[test]
fn test_add_with_bigint() {
    let result = eval_str("(+ 9223372036854775808 1)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "9223372036854775809N");
}

#[test]
fn test_sub_with_bigint() {
    let result = eval_str("(- 9223372036854775808 1)").unwrap();
    // Result fits in i64, so it should demote
    assert!(matches!(result, KlujurVal::Int(_)));
    assert_eq!(result, KlujurVal::int(9223372036854775807));
}

#[test]
fn test_mul_with_bigint() {
    let result = eval_str("(* 9223372036854775808 2)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
}

#[test]
fn test_div_with_bigint() {
    let result = eval_str("(/ 9223372036854775808 2)").unwrap();
    // Division produces BigRatio, which simplifies to Int if possible
    // 9223372036854775808 / 2 = 4611686018427387904 (fits in i64)
    assert_eq!(result, KlujurVal::int(4611686018427387904));
}

#[test]
fn test_quot_with_bigint() {
    let result = eval_str("(quot 9223372036854775808 3)").unwrap();
    // Result fits in i64, so it demotes to Int
    assert!(matches!(result, KlujurVal::Int(_) | KlujurVal::BigInt(_)));
}

#[test]
fn test_rem_with_bigint() {
    let result = eval_str("(rem 9223372036854775808 3)").unwrap();
    // Remainder fits in i64
    assert!(matches!(result, KlujurVal::Int(_) | KlujurVal::BigInt(_)));
}

#[test]
fn test_mod_with_bigint() {
    let result = eval_str("(mod 9223372036854775808 7)").unwrap();
    assert!(matches!(result, KlujurVal::Int(_) | KlujurVal::BigInt(_)));
}

// =============================================================================
// Predicates
// =============================================================================

#[test]
fn test_bigint_predicate() {
    assert_eq!(eval_str("(bigint? 42)").unwrap(), KlujurVal::bool(false));
    assert_eq!(
        eval_str("(bigint? 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
}

#[test]
fn test_integer_predicate_includes_bigint() {
    assert_eq!(eval_str("(integer? 42)").unwrap(), KlujurVal::bool(true));
    assert_eq!(
        eval_str("(integer? 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(eval_str("(integer? 3.14)").unwrap(), KlujurVal::bool(false));
}

#[test]
fn test_number_predicate_includes_bigint() {
    assert_eq!(eval_str("(number? 42)").unwrap(), KlujurVal::bool(true));
    assert_eq!(
        eval_str("(number? 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
}

#[test]
fn test_even_odd_with_bigint() {
    assert_eq!(
        eval_str("(even? 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(
        eval_str("(odd? 9223372036854775809)").unwrap(),
        KlujurVal::bool(true)
    );
}

#[test]
fn test_pos_neg_zero_with_bigint() {
    assert_eq!(
        eval_str("(pos? 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(
        eval_str("(neg? -9223372036854775809)").unwrap(),
        KlujurVal::bool(true)
    );
}

// =============================================================================
// Comparison operators
// =============================================================================

#[test]
fn test_equality_bigint_vs_int() {
    // BigInt that fits in i64 should equal the int
    assert_eq!(
        eval_str("(= 9223372036854775807 9223372036854775807)").unwrap(),
        KlujurVal::bool(true)
    );
}

#[test]
fn test_comparison_bigint() {
    assert_eq!(
        eval_str("(< 9223372036854775807 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(
        eval_str("(> 9223372036854775808 9223372036854775807)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(
        eval_str("(<= 9223372036854775808 9223372036854775808)").unwrap(),
        KlujurVal::bool(true)
    );
    assert_eq!(
        eval_str("(>= 9223372036854775808 1)").unwrap(),
        KlujurVal::bool(true)
    );
}

// =============================================================================
// Type conversion
// =============================================================================

#[test]
fn test_double_with_bigint() {
    // Converting BigInt to float
    let result = eval_str("(double 9223372036854775808)").unwrap();
    assert!(matches!(result, KlujurVal::Float(_)));
}

#[test]
fn test_int_with_bigint_in_range() {
    // BigInt that fits in i64 can be converted
    let result = eval_str("(int 9223372036854775807)").unwrap();
    assert!(matches!(result, KlujurVal::Int(_)));
}

#[test]
fn test_int_with_bigint_out_of_range() {
    // BigInt too large for i64 should error
    let result = eval_str("(int 9223372036854775808)");
    assert!(result.is_err());
}

// =============================================================================
// Abs with BigInt
// =============================================================================

#[test]
fn test_abs_with_bigint() {
    let result = eval_str("(abs -9223372036854775809)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
    assert_eq!(result.to_string(), "9223372036854775809N");
}

// =============================================================================
// Max/Min with BigInt
// =============================================================================

#[test]
fn test_max_with_bigint() {
    let result = eval_str("(max 9223372036854775807 9223372036854775808)").unwrap();
    assert!(matches!(result, KlujurVal::BigInt(_)));
}

#[test]
fn test_min_with_bigint() {
    let result = eval_str("(min 9223372036854775807 9223372036854775808)").unwrap();
    assert!(matches!(result, KlujurVal::Int(_)));
}
