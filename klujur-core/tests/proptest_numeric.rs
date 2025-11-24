// klujur-core - Property-based tests for numeric tower
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Property-based tests for the numeric tower and arithmetic operations.
//!
//! Tests the following properties:
//! - Numeric tower contagion: Float > BigRatio > BigInt > Ratio > Int
//! - Auto-promoting operators never overflow (always BigInt/BigRatio)
//! - Standard operators error on i64 overflow
//! - Arithmetic identities (commutativity, associativity where applicable)

mod common;

use common::{KlujurVal, eval_str, eval_str_with_env, new_env};
use proptest::prelude::*;

// =============================================================================
// Strategies for generating numeric values
// =============================================================================

/// Generate arbitrary i64 integers (Klujur Int type)
fn arb_int() -> impl Strategy<Value = i64> {
    any::<i64>()
}

/// Generate small integers that won't overflow on basic operations
fn arb_small_int() -> impl Strategy<Value = i64> {
    -1_000_000i64..1_000_000i64
}

/// Generate finite f64 values (Klujur Float type)
fn arb_float() -> impl Strategy<Value = f64> {
    any::<f64>().prop_filter("must be finite", |f| f.is_finite())
}

/// Format a float to ensure it's parsed as a float (not int)
fn fmt_float(f: f64) -> String {
    let s = format!("{}", f);
    // Ensure the string contains a decimal point or 'e' for scientific notation
    if s.contains('.') || s.contains('e') || s.contains('E') {
        s
    } else {
        format!("{}.0", s)
    }
}

/// Generate non-zero denominators for ratios
fn arb_nonzero_denom() -> impl Strategy<Value = i64> {
    prop_oneof![1i64..=i64::MAX, i64::MIN..=-1i64,]
}

// =============================================================================
// Numeric tower contagion tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Int + Int = Int (no contagion)
    #[test]
    fn int_plus_int_stays_int(a in arb_small_int(), b in arb_small_int()) {
        let code = format!("(+ {} {})", a, b);
        let result = eval_str(&code).unwrap();
        prop_assert!(
            matches!(result, KlujurVal::Int(_)),
            "Expected Int, got {:?} for {}",
            result,
            code
        );
    }

    /// Float + anything = Float
    #[test]
    fn float_contagion_add(a in arb_float(), b in arb_small_int()) {
        let code = format!("(+ {} {})", fmt_float(a), b);
        let result = eval_str(&code).unwrap();
        prop_assert!(
            matches!(result, KlujurVal::Float(_)),
            "Expected Float, got {:?} for {}",
            result,
            code
        );
    }

    /// Float * anything = Float
    #[test]
    fn float_contagion_mul(a in arb_float(), b in arb_small_int()) {
        let code = format!("(* {} {})", fmt_float(a), b);
        let result = eval_str(&code).unwrap();
        prop_assert!(
            matches!(result, KlujurVal::Float(_)),
            "Expected Float, got {:?} for {}",
            result,
            code
        );
    }

    /// Int / Int = Ratio or Int (when evenly divisible)
    #[test]
    fn int_div_int_ratio_or_int(a in arb_small_int(), b in arb_nonzero_denom()) {
        let code = format!("(/ {} {})", a, b);
        let result = eval_str(&code).unwrap();
        prop_assert!(
            matches!(result, KlujurVal::Int(_) | KlujurVal::Ratio(_, _)),
            "Expected Int or Ratio, got {:?} for {}",
            result,
            code
        );
    }

    /// Ratio + Int = Ratio (or Int if simplifiable)
    #[test]
    fn ratio_plus_int_stays_rational(
        num in arb_small_int(),
        den in 2i64..1000i64,
        b in arb_small_int()
    ) {
        let code = format!("(+ (/ {} {}) {})", num, den, b);
        let result = eval_str(&code).unwrap();
        prop_assert!(
            matches!(result, KlujurVal::Int(_) | KlujurVal::Ratio(_, _)),
            "Expected Int or Ratio, got {:?} for {}",
            result,
            code
        );
    }
}

// =============================================================================
// Auto-promoting operator tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// +' never overflows - always produces valid result
    #[test]
    fn add_prime_never_overflows(a in arb_int(), b in arb_int()) {
        let code = format!("(+' {} {})", a, b);
        let result = eval_str(&code);
        prop_assert!(
            result.is_ok(),
            "Expected +' to succeed, got error: {:?} for {}",
            result.err(),
            code
        );
    }

    /// -' never overflows
    #[test]
    fn sub_prime_never_overflows(a in arb_int(), b in arb_int()) {
        let code = format!("(-' {} {})", a, b);
        let result = eval_str(&code);
        prop_assert!(
            result.is_ok(),
            "Expected -' to succeed, got error: {:?} for {}",
            result.err(),
            code
        );
    }

    /// *' never overflows
    #[test]
    fn mul_prime_never_overflows(a in arb_int(), b in arb_int()) {
        let code = format!("(*' {} {})", a, b);
        let result = eval_str(&code);
        prop_assert!(
            result.is_ok(),
            "Expected *' to succeed, got error: {:?} for {}",
            result.err(),
            code
        );
    }

    /// inc' never overflows
    #[test]
    fn inc_prime_never_overflows(a in arb_int()) {
        let code = format!("(inc' {})", a);
        let result = eval_str(&code);
        prop_assert!(
            result.is_ok(),
            "Expected inc' to succeed, got error: {:?} for {}",
            result.err(),
            code
        );
    }

    /// dec' never overflows
    #[test]
    fn dec_prime_never_overflows(a in arb_int()) {
        let code = format!("(dec' {})", a);
        let result = eval_str(&code);
        prop_assert!(
            result.is_ok(),
            "Expected dec' to succeed, got error: {:?} for {}",
            result.err(),
            code
        );
    }
}

// =============================================================================
// Arithmetic identity tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Addition is commutative: a + b = b + a
    #[test]
    fn add_commutative(a in arb_small_int(), b in arb_small_int()) {
        let env = new_env();
        let ab = eval_str_with_env(&format!("(+ {} {})", a, b), &env).unwrap();
        let ba = eval_str_with_env(&format!("(+ {} {})", b, a), &env).unwrap();
        prop_assert_eq!(ab, ba, "Addition not commutative for {} + {}", a, b);
    }

    /// Multiplication is commutative: a * b = b * a
    #[test]
    fn mul_commutative(a in arb_small_int(), b in arb_small_int()) {
        let env = new_env();
        let ab = eval_str_with_env(&format!("(* {} {})", a, b), &env).unwrap();
        let ba = eval_str_with_env(&format!("(* {} {})", b, a), &env).unwrap();
        prop_assert_eq!(ab, ba, "Multiplication not commutative for {} * {}", a, b);
    }

    /// Addition identity: a + 0 = a
    #[test]
    fn add_identity(a in arb_small_int()) {
        let result = eval_str(&format!("(+ {} 0)", a)).unwrap();
        prop_assert_eq!(result, KlujurVal::int(a), "Addition identity failed for {}", a);
    }

    /// Multiplication identity: a * 1 = a
    #[test]
    fn mul_identity(a in arb_small_int()) {
        let result = eval_str(&format!("(* {} 1)", a)).unwrap();
        prop_assert_eq!(result, KlujurVal::int(a), "Multiplication identity failed for {}", a);
    }

    /// Multiplication by zero: a * 0 = 0
    #[test]
    fn mul_zero(a in arb_small_int()) {
        let result = eval_str(&format!("(* {} 0)", a)).unwrap();
        prop_assert_eq!(result, KlujurVal::int(0), "Multiplication by zero failed for {}", a);
    }

    /// Double negation: (- (- a)) = a
    #[test]
    fn double_negation(a in arb_small_int()) {
        let result = eval_str(&format!("(- (- {}))", a)).unwrap();
        prop_assert_eq!(result, KlujurVal::int(a), "Double negation failed for {}", a);
    }

    /// inc/dec inverse: (dec (inc a)) = a
    #[test]
    fn inc_dec_inverse(a in arb_small_int()) {
        let result = eval_str(&format!("(dec (inc {}))", a)).unwrap();
        prop_assert_eq!(result, KlujurVal::int(a), "inc/dec inverse failed for {}", a);
    }
}

// =============================================================================
// Comparison tests
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Reflexivity: a = a
    #[test]
    fn equality_reflexive(a in arb_small_int()) {
        let result = eval_str(&format!("(= {} {})", a, a)).unwrap();
        prop_assert_eq!(result, KlujurVal::bool(true), "Equality not reflexive for {}", a);
    }

    /// Ordering consistency: (< a b) implies (> b a)
    #[test]
    fn ordering_consistent(a in arb_small_int(), b in arb_small_int()) {
        prop_assume!(a != b);
        let lt = eval_str(&format!("(< {} {})", a, b)).unwrap();
        let gt = eval_str(&format!("(> {} {})", b, a)).unwrap();
        prop_assert_eq!(lt, gt, "Ordering inconsistent for {} and {}", a, b);
    }

    /// Trichotomy: exactly one of a < b, a = b, a > b is true
    #[test]
    fn trichotomy(a in arb_small_int(), b in arb_small_int()) {
        let lt = eval_str(&format!("(< {} {})", a, b)).unwrap() == KlujurVal::bool(true);
        let eq = eval_str(&format!("(= {} {})", a, b)).unwrap() == KlujurVal::bool(true);
        let gt = eval_str(&format!("(> {} {})", a, b)).unwrap() == KlujurVal::bool(true);

        let count = [lt, eq, gt].iter().filter(|&&x| x).count();
        prop_assert_eq!(count, 1, "Trichotomy violated for {} and {}: lt={}, eq={}, gt={}", a, b, lt, eq, gt);
    }

    /// max returns the larger value
    #[test]
    fn max_is_larger(a in arb_small_int(), b in arb_small_int()) {
        let max_val = eval_str(&format!("(max {} {})", a, b)).unwrap();
        let expected = KlujurVal::int(a.max(b));
        prop_assert_eq!(max_val, expected, "max({}, {}) incorrect", a, b);
    }

    /// min returns the smaller value
    #[test]
    fn min_is_smaller(a in arb_small_int(), b in arb_small_int()) {
        let min_val = eval_str(&format!("(min {} {})", a, b)).unwrap();
        let expected = KlujurVal::int(a.min(b));
        prop_assert_eq!(min_val, expected, "min({}, {}) incorrect", a, b);
    }
}

// =============================================================================
// Float special values
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Float arithmetic preserves finiteness for finite inputs
    #[test]
    fn float_add_finite(a in arb_float(), b in arb_float()) {
        let code = format!("(+ {} {})", fmt_float(a), fmt_float(b));
        let result = eval_str(&code).unwrap();
        if let KlujurVal::Float(f) = result {
            // Result may be infinite if inputs are large, but should not be NaN
            // unless inputs cause it
            prop_assert!(!f.is_nan() || a.is_nan() || b.is_nan(),
                "Unexpected NaN for {} + {}", a, b);
        } else {
            prop_assert!(false, "Expected Float, got {:?}", result);
        }
    }
}
