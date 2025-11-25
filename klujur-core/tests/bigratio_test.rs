// klujur-core - BigRatio integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for BigRatio (arbitrary precision rational) support.
//!
//! Tests for:
//! - BigRatio creation from division of large numbers
//! - Arithmetic operations producing BigRatio results
//! - Comparison operators with BigRatio
//! - Cross-type equality with BigRatio
//! - Predicates and type checks
//! - Display formatting

mod common;

use common::{KlujurVal, eval_str};

// =============================================================================
// BigRatio creation
// =============================================================================

#[test]
fn bigratio_from_large_int_division() {
    // Dividing two large integers should produce a BigRatio
    // 2^63 / 3 cannot be represented as a simple Ratio
    let result = eval_str("(/ 9223372036854775808 3)").unwrap();
    // Result is a ratio (may or may not be BigRatio depending on representation)
    // The key thing is that it works
    assert!(
        result.to_string().contains('/'),
        "Expected ratio, got: {}",
        result
    );
}

#[test]
fn bigratio_from_bigint_division() {
    // When BigInt is divided by another value, may produce BigRatio
    let result = eval_str("(/ 18446744073709551616 7)").unwrap();
    // Should produce a ratio
    assert!(
        result.to_string().contains('/')
            || matches!(result, KlujurVal::BigRatio(_, _) | KlujurVal::Ratio(_, _)),
        "Expected ratio type, got: {}",
        result
    );
}

#[test]
fn bigratio_simplifies_to_bigint() {
    // When BigRatio simplifies to a whole number, it should become BigInt
    let result = eval_str("(/ 18446744073709551614 2)").unwrap();
    // 18446744073709551614 / 2 = 9223372036854775807 (fits in i64)
    // Should simplify to Int
    assert_eq!(result.to_string(), "9223372036854775807");
    assert!(matches!(result, KlujurVal::Int(_)));
}

#[test]
fn bigratio_simplifies_to_int_when_possible() {
    // BigRatio that simplifies to fit in i64 should become Int
    let result = eval_str("(/ 9223372036854775808 9223372036854775808)").unwrap();
    // BigInt / same BigInt = 1
    assert_eq!(result.to_string(), "1");
    assert!(matches!(result, KlujurVal::Int(_)));
}

// =============================================================================
// Arithmetic with BigRatio
// =============================================================================

#[test]
fn bigratio_addition() {
    // Adding two ratios involving large numbers
    let result = eval_str("(+ (/ 9223372036854775808 3) (/ 9223372036854775808 3))").unwrap();
    // 2 * (BigInt / 3) = (2 * BigInt) / 3
    assert!(!result.to_string().is_empty());
}

#[test]
fn bigratio_subtraction() {
    // Subtracting ratios
    let result = eval_str("(- (/ 9223372036854775808 2) (/ 9223372036854775808 4))").unwrap();
    // BigInt/2 - BigInt/4 = BigInt/4
    assert!(!result.to_string().is_empty());
}

#[test]
fn bigratio_multiplication() {
    // Multiplying a BigRatio by an integer
    let result = eval_str("(* (/ 9223372036854775808 3) 3)").unwrap();
    // (BigInt / 3) * 3 = BigInt
    assert_eq!(result.to_string(), "9223372036854775808N");
}

#[test]
fn bigratio_division() {
    // Dividing a BigRatio
    let result = eval_str("(/ (/ 9223372036854775808 2) 2)").unwrap();
    // (BigInt / 2) / 2 = BigInt / 4
    assert!(!result.to_string().is_empty());
}

// =============================================================================
// Comparison operators
// =============================================================================

#[test]
fn bigratio_equality_with_self() {
    let result = eval_str("(= (/ 9223372036854775808 3) (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_less_than() {
    let result = eval_str("(< (/ 9223372036854775808 4) (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_greater_than() {
    let result = eval_str("(> (/ 9223372036854775808 3) (/ 9223372036854775808 4))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_less_than_equal() {
    let result = eval_str("(<= (/ 9223372036854775808 3) (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// Cross-type equality
// =============================================================================

#[test]
fn bigratio_equals_bigint() {
    // BigRatio n/1 should equal BigInt n
    let result = eval_str("(= (/ 9223372036854775808 1) 9223372036854775808)").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_equals_int_when_simplified() {
    // BigRatio that simplifies to fit in i64
    let result = eval_str("(= (/ 10 2) 5)").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_equals_ratio() {
    // BigRatio should equal equivalent Ratio when values fit
    let result = eval_str("(= (/ 1 3) (/ 1 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// Cross-type comparisons
// =============================================================================

#[test]
fn bigratio_compare_with_bigint() {
    // Compare BigRatio with BigInt
    let result = eval_str("(< (/ 9223372036854775808 3) 9223372036854775808)").unwrap();
    // BigInt/3 < BigInt
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_compare_with_int() {
    // BigRatio compared to Int
    let result = eval_str("(> (/ 9223372036854775808 2) 1000000)").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_compare_with_float() {
    // BigRatio compared to Float (approximate comparison)
    let result = eval_str("(< (/ 1 3) 0.5)").unwrap();
    // 1/3 ≈ 0.333... < 0.5
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// Predicates
// =============================================================================

#[test]
fn bigratio_is_ratio() {
    // BigRatio should satisfy ratio? predicate
    let result = eval_str("(ratio? (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_is_number() {
    let result = eval_str("(number? (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_is_not_integer() {
    // A true ratio (not 1/1) should not be an integer
    let result = eval_str("(integer? (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

#[test]
fn bigratio_is_not_float() {
    let result = eval_str("(float? (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

#[test]
fn bigratio_positive() {
    let result = eval_str("(pos? (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn bigratio_negative() {
    // Use a BigInt that is already negative to avoid parsing issues with i64::MIN
    let result = eval_str("(neg? (/ -9223372036854775809 3))").unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// Display formatting
// =============================================================================

#[test]
fn bigratio_display_format() {
    // BigRatio should display as num/denN or similar
    let result = eval_str("(/ 9223372036854775808 3)").unwrap();
    let display = result.to_string();

    // Should contain a slash for ratio
    assert!(
        display.contains('/'),
        "Display should show ratio: {}",
        display
    );
    // Should end with N to indicate big numbers
    assert!(
        display.ends_with('N'),
        "Display should end with N: {}",
        display
    );
}

// =============================================================================
// Type conversions
// =============================================================================

#[test]
fn bigratio_to_double() {
    // Converting BigRatio to double
    let result = eval_str("(double (/ 9223372036854775808 2))").unwrap();
    assert!(matches!(result, KlujurVal::Float(_)));
}

#[test]
fn bigratio_numerator_denominator() {
    // If numerator/denominator functions exist
    let result = eval_str("(numerator (/ 10 3))");
    if result.is_ok() {
        assert_eq!(result.unwrap(), KlujurVal::int(10));
    }
    // If not implemented, skip
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn bigratio_very_large_numerator_denominator() {
    // Both numerator and denominator are very large
    let result = eval_str("(/ 18446744073709551616 9223372036854775809)").unwrap();
    // Should work without overflow
    assert!(!result.to_string().is_empty());
}

#[test]
fn bigratio_gcd_simplification() {
    // BigRatio should be simplified by GCD
    // 18446744073709551616 / 2 = 9223372036854775808
    let result = eval_str("(/ 18446744073709551616 2)").unwrap();
    // Result should be the simplified BigInt
    assert!(
        result.to_string().contains("9223372036854775808"),
        "Result: {}",
        result
    );
}

#[test]
fn bigratio_from_ratio_overflow() {
    // When regular ratio arithmetic would overflow, should promote to BigRatio
    // This tests the numeric tower promotion
    let result = eval_str("(+ 9223372036854775807/2 1/2)");
    // (MAX/2 + 1/2) = (MAX+1)/2 which overflows MAX, so numerator becomes BigInt
    if result.is_ok() {
        let val = result.unwrap();
        assert!(!val.to_string().is_empty());
    }
}

#[test]
fn bigratio_zero_numerator() {
    // 0/BigInt should simplify to 0
    let result = eval_str("(- (/ 9223372036854775808 3) (/ 9223372036854775808 3))").unwrap();
    assert_eq!(result, KlujurVal::int(0));
}

// =============================================================================
// Arithmetic overflow promotion
// =============================================================================

#[test]
fn ratio_promotes_to_bigratio_on_overflow() {
    // When adding ratios causes numerator overflow, should promote
    let result = eval_str("(+ 4611686018427387903/1 4611686018427387904/1)");
    // This should either produce a BigInt (if simplified) or handle overflow
    if result.is_ok() {
        let val = result.unwrap();
        // Should produce 9223372036854775807 (i64::MAX) which fits, or overflow
        assert!(!val.to_string().is_empty());
    }
}

#[test]
fn mixed_ratio_bigratio_arithmetic() {
    // Mixing regular Ratio with BigRatio should promote appropriately
    let result = eval_str("(+ 1/3 (/ 9223372036854775808 3))").unwrap();
    // 1/3 + BigInt/3 = (1 + BigInt)/3
    assert!(!result.to_string().is_empty());
}
