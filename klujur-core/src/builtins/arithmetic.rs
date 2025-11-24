// klujur-core - Arithmetic built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Arithmetic operations: +, -, *, /, quot, rem, mod, inc, dec, max, min, abs
//!
//! ## Integer Overflow Behaviour
//!
//! Unlike Clojure, which automatically promotes to BigInteger on overflow,
//! Klujur uses checked arithmetic and returns an error on integer overflow.
//! This includes operations: +, -, *, inc, dec, abs (for i64::MIN), and
//! unary negation (for i64::MIN).
//!
//! Operations involving floats do not check for overflow.

use klujur_parser::{BigInt, KlujurVal, ToPrimitive};

use crate::error::{Error, Result};

use super::compare_numbers;

// ============================================================================
// Helper functions for numeric arithmetic
// ============================================================================

/// Convert a numeric value to f64.
fn to_float(val: &KlujurVal) -> Result<f64> {
    match val {
        KlujurVal::Int(n) => Ok(*n as f64),
        KlujurVal::BigInt(n) => Ok(n.to_f64().unwrap_or(f64::INFINITY)),
        KlujurVal::Float(n) => Ok(*n),
        KlujurVal::Ratio(num, den) => Ok(*num as f64 / *den as f64),
        KlujurVal::BigRatio(num, den) => {
            // Handle cases where numerator and/or denominator overflow f64.
            // If both overflow, INFINITY / INFINITY = NaN, which is wrong.
            // Instead, use BigInt division to compute an approximation.
            match (num.to_f64(), den.to_f64()) {
                (Some(nf), Some(df)) => Ok(nf / df),
                (Some(nf), None) => {
                    // Denominator too large to fit in f64, result approaches 0
                    Ok(if nf.is_sign_negative() { -0.0 } else { 0.0 })
                }
                (None, Some(df)) => {
                    // Numerator too large, result is +/- infinity
                    use num_bigint::Sign;
                    let num_neg = num.sign() == Sign::Minus;
                    let den_neg = df < 0.0;
                    let result_neg = num_neg != den_neg;
                    Ok(if result_neg {
                        f64::NEG_INFINITY
                    } else {
                        f64::INFINITY
                    })
                }
                (None, None) => {
                    // Both too large - use BigInt division for approximation
                    let quotient = num / den;
                    let result_neg = num.sign() != den.sign();
                    Ok(quotient.to_f64().unwrap_or(if result_neg {
                        f64::NEG_INFINITY
                    } else {
                        f64::INFINITY
                    }))
                }
            }
        }
        other => Err(Error::type_error_in(
            "arithmetic",
            "number",
            other.type_name(),
        )),
    }
}

/// Convert a numeric value to an i64 ratio (numerator, denominator).
///
/// This function only handles `Int` and `Ratio` types. For `BigInt` and `BigRatio`,
/// use `to_bigratio` instead. The numeric tower dispatch logic in arithmetic
/// operations ensures this function is only called for appropriate types.
fn to_i64_ratio(val: &KlujurVal) -> Result<(i64, i64)> {
    match val {
        KlujurVal::Int(n) => Ok((*n, 1)),
        KlujurVal::Ratio(num, den) => Ok((*num, *den)),
        other => Err(Error::type_error_in(
            "arithmetic",
            "number",
            other.type_name(),
        )),
    }
}

/// Convert a numeric value to a BigInt ratio (numerator, denominator).
fn to_bigratio(val: &KlujurVal) -> Result<(BigInt, BigInt)> {
    match val {
        KlujurVal::Int(n) => Ok((BigInt::from(*n), BigInt::from(1))),
        KlujurVal::BigInt(n) => Ok((n.clone(), BigInt::from(1))),
        KlujurVal::Ratio(num, den) => Ok((BigInt::from(*num), BigInt::from(*den))),
        KlujurVal::BigRatio(num, den) => Ok((num.clone(), den.clone())),
        other => Err(Error::type_error_in(
            "arithmetic",
            "number",
            other.type_name(),
        )),
    }
}

/// Convert a numeric value to BigInt (for integer operations).
fn to_bigint(val: &KlujurVal) -> Result<BigInt> {
    match val {
        KlujurVal::Int(n) => Ok(BigInt::from(*n)),
        KlujurVal::BigInt(n) => Ok(n.clone()),
        other => Err(Error::type_error_in(
            "arithmetic",
            "integer",
            other.type_name(),
        )),
    }
}

/// Numeric type category for determining arithmetic precision.
///
/// The numeric tower follows the precedence: Float > BigRatio > BigInt > Ratio > Int
/// However, combining BigInt with Ratio produces BigRatio (not BigInt).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumericCategory {
    /// All values are i64 integers
    Int,
    /// At least one i64 ratio (no BigInt or BigRatio)
    Ratio,
    /// At least one BigInt (no ratios)
    BigInt,
    /// BigRatio present, or BigInt + Ratio combination
    BigRatio,
    /// At least one Float (highest precedence)
    Float,
}

/// Classify numeric arguments in a single pass, returning the appropriate category.
///
/// Short-circuits immediately on Float (highest precedence) for performance.
/// Returns an error if any argument is not a numeric type.
fn classify_numeric_args(args: &[KlujurVal]) -> Result<NumericCategory> {
    let mut has_bigint = false;
    let mut has_bigratio = false;
    let mut has_ratio = false;

    for arg in args {
        match arg {
            KlujurVal::Int(_) => {}
            KlujurVal::Ratio(_, _) => has_ratio = true,
            KlujurVal::BigInt(_) => has_bigint = true,
            KlujurVal::BigRatio(_, _) => has_bigratio = true,
            KlujurVal::Float(_) => return Ok(NumericCategory::Float), // Short-circuit
            other => {
                return Err(Error::type_error_in(
                    "arithmetic",
                    "number",
                    other.type_name(),
                ));
            }
        }
    }

    // Determine final category based on flags
    Ok(if has_bigratio || (has_bigint && has_ratio) {
        NumericCategory::BigRatio
    } else if has_bigint {
        NumericCategory::BigInt
    } else if has_ratio {
        NumericCategory::Ratio
    } else {
        NumericCategory::Int
    })
}

// ============================================================================
// Arithmetic
// ============================================================================

pub(crate) fn builtin_add(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(0));
    }

    match classify_numeric_args(args)? {
        NumericCategory::Float => {
            let mut sum: f64 = 0.0;
            for arg in args {
                sum += to_float(arg)?;
            }
            Ok(KlujurVal::float(sum))
        }
        NumericCategory::BigRatio => {
            let mut num = BigInt::from(0);
            let mut den = BigInt::from(1);
            for arg in args {
                let (n, d) = to_bigratio(arg)?;
                // num/den + n/d = (num*d + n*den) / (den*d)
                num = &num * &d + &n * &den;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        NumericCategory::BigInt => {
            let mut sum = BigInt::from(0);
            for arg in args {
                sum += to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(sum))
        }
        NumericCategory::Ratio => {
            let mut num: i64 = 0;
            let mut den: i64 = 1;
            for arg in args {
                let (n, d) = to_i64_ratio(arg)?;
                // num/den + n/d = (num*d + n*den) / (den*d)
                num = num
                    .checked_mul(d)
                    .and_then(|nd| n.checked_mul(den).and_then(|nd2| nd.checked_add(nd2)))
                    .ok_or(Error::IntegerOverflow { operation: "+" })?;
                den = den
                    .checked_mul(d)
                    .ok_or(Error::IntegerOverflow { operation: "+" })?;
            }
            Ok(KlujurVal::ratio(num, den))
        }
        NumericCategory::Int => {
            let mut int_sum: i64 = 0;
            for arg in args {
                match arg {
                    KlujurVal::Int(n) => {
                        int_sum = int_sum
                            .checked_add(*n)
                            .ok_or(Error::IntegerOverflow { operation: "+" })?;
                    }
                    other => {
                        return Err(Error::type_error_in("+", "number", other.type_name()));
                    }
                }
            }
            Ok(KlujurVal::int(int_sum))
        }
    }
}

/// Simplified category for auto-promoting operations (`+'`, `-'`, `*'`).
/// These always use BigInt/BigRatio to avoid overflow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PromotingCategory {
    /// Use BigInt arithmetic
    BigInt,
    /// Use BigRatio arithmetic (has any ratio type)
    BigRatio,
    /// Use Float arithmetic
    Float,
}

/// Classify numeric arguments for auto-promoting operations.
/// Short-circuits on Float for performance.
fn classify_promoting_args(args: &[KlujurVal]) -> Result<PromotingCategory> {
    let mut has_ratio = false;

    for arg in args {
        match arg {
            KlujurVal::Int(_) | KlujurVal::BigInt(_) => {}
            KlujurVal::Ratio(_, _) | KlujurVal::BigRatio(_, _) => has_ratio = true,
            KlujurVal::Float(_) => return Ok(PromotingCategory::Float),
            other => {
                return Err(Error::type_error_in(
                    "arithmetic",
                    "number",
                    other.type_name(),
                ));
            }
        }
    }

    Ok(if has_ratio {
        PromotingCategory::BigRatio
    } else {
        PromotingCategory::BigInt
    })
}

/// Auto-promoting addition that promotes to BigInt on overflow.
pub(crate) fn builtin_add_prime(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(0));
    }

    match classify_promoting_args(args)? {
        PromotingCategory::Float => {
            let mut sum: f64 = 0.0;
            for arg in args {
                sum += to_float(arg)?;
            }
            Ok(KlujurVal::float(sum))
        }
        PromotingCategory::BigRatio => {
            let mut num = BigInt::from(0);
            let mut den = BigInt::from(1);
            for arg in args {
                let (n, d) = to_bigratio(arg)?;
                num = &num * &d + &n * &den;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        PromotingCategory::BigInt => {
            let mut sum = BigInt::from(0);
            for arg in args {
                sum += to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(sum))
        }
    }
}

pub(crate) fn builtin_sub(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // Unary negation
        return match &args[0] {
            KlujurVal::Int(n) => Ok(KlujurVal::int(
                n.checked_neg()
                    .ok_or(Error::IntegerOverflow { operation: "-" })?,
            )),
            KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(-n)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(-n)),
            KlujurVal::Ratio(num, den) => {
                let neg_num = num
                    .checked_neg()
                    .ok_or(Error::IntegerOverflow { operation: "-" })?;
                Ok(KlujurVal::ratio(neg_num, *den))
            }
            KlujurVal::BigRatio(num, den) => Ok(KlujurVal::bigratio(-num, den.clone())),
            other => Err(Error::type_error_in("-", "number", other.type_name())),
        };
    }

    match classify_numeric_args(args)? {
        NumericCategory::Float => {
            let mut result = to_float(&args[0])?;
            for arg in &args[1..] {
                result -= to_float(arg)?;
            }
            Ok(KlujurVal::float(result))
        }
        NumericCategory::BigRatio => {
            let (mut num, mut den) = to_bigratio(&args[0])?;
            for arg in &args[1..] {
                let (n, d) = to_bigratio(arg)?;
                num = &num * &d - &n * &den;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        NumericCategory::BigInt => {
            let mut result = to_bigint(&args[0])?;
            for arg in &args[1..] {
                result -= to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(result))
        }
        NumericCategory::Ratio => {
            let (mut num, mut den) = to_i64_ratio(&args[0])?;
            for arg in &args[1..] {
                let (n, d) = to_i64_ratio(arg)?;
                num = num
                    .checked_mul(d)
                    .and_then(|nd| n.checked_mul(den).and_then(|nd2| nd.checked_sub(nd2)))
                    .ok_or(Error::IntegerOverflow { operation: "-" })?;
                den = den
                    .checked_mul(d)
                    .ok_or(Error::IntegerOverflow { operation: "-" })?;
            }
            Ok(KlujurVal::ratio(num, den))
        }
        NumericCategory::Int => {
            let mut int_result = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("-", "number", other.type_name())),
            };
            for arg in &args[1..] {
                match arg {
                    KlujurVal::Int(n) => {
                        int_result = int_result
                            .checked_sub(*n)
                            .ok_or(Error::IntegerOverflow { operation: "-" })?;
                    }
                    other => {
                        return Err(Error::type_error_in("-", "number", other.type_name()));
                    }
                }
            }
            Ok(KlujurVal::int(int_result))
        }
    }
}

/// Auto-promoting subtraction that promotes to BigInt on overflow.
pub(crate) fn builtin_sub_prime(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // Unary negation - always safe with BigInt
        return match &args[0] {
            KlujurVal::Int(n) => Ok(KlujurVal::bigint(-BigInt::from(*n))),
            KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(-n)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(-n)),
            KlujurVal::Ratio(num, den) => {
                Ok(KlujurVal::bigratio(-BigInt::from(*num), BigInt::from(*den)))
            }
            KlujurVal::BigRatio(num, den) => Ok(KlujurVal::bigratio(-num, den.clone())),
            other => Err(Error::type_error_in("-'", "number", other.type_name())),
        };
    }

    match classify_promoting_args(args)? {
        PromotingCategory::Float => {
            let mut result = to_float(&args[0])?;
            for arg in &args[1..] {
                result -= to_float(arg)?;
            }
            Ok(KlujurVal::float(result))
        }
        PromotingCategory::BigRatio => {
            let (mut num, mut den) = to_bigratio(&args[0])?;
            for arg in &args[1..] {
                let (n, d) = to_bigratio(arg)?;
                num = &num * &d - &n * &den;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        PromotingCategory::BigInt => {
            let mut result = to_bigint(&args[0])?;
            for arg in &args[1..] {
                result -= to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(result))
        }
    }
}

pub(crate) fn builtin_mul(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(1));
    }

    match classify_numeric_args(args)? {
        NumericCategory::Float => {
            let mut prod: f64 = 1.0;
            for arg in args {
                prod *= to_float(arg)?;
            }
            Ok(KlujurVal::float(prod))
        }
        NumericCategory::BigRatio => {
            let mut num = BigInt::from(1);
            let mut den = BigInt::from(1);
            for arg in args {
                let (n, d) = to_bigratio(arg)?;
                num = &num * &n;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        NumericCategory::BigInt => {
            let mut prod = BigInt::from(1);
            for arg in args {
                prod *= to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(prod))
        }
        NumericCategory::Ratio => {
            let mut num: i64 = 1;
            let mut den: i64 = 1;
            for arg in args {
                let (n, d) = to_i64_ratio(arg)?;
                // (num/den) * (n/d) = (num*n) / (den*d)
                num = num
                    .checked_mul(n)
                    .ok_or(Error::IntegerOverflow { operation: "*" })?;
                den = den
                    .checked_mul(d)
                    .ok_or(Error::IntegerOverflow { operation: "*" })?;
            }
            Ok(KlujurVal::ratio(num, den))
        }
        NumericCategory::Int => {
            let mut int_prod: i64 = 1;
            for arg in args {
                match arg {
                    KlujurVal::Int(n) => {
                        int_prod = int_prod
                            .checked_mul(*n)
                            .ok_or(Error::IntegerOverflow { operation: "*" })?;
                    }
                    other => {
                        return Err(Error::type_error_in("*", "number", other.type_name()));
                    }
                }
            }
            Ok(KlujurVal::int(int_prod))
        }
    }
}

/// Auto-promoting multiplication that promotes to BigInt on overflow.
pub(crate) fn builtin_mul_prime(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(1));
    }

    match classify_promoting_args(args)? {
        PromotingCategory::Float => {
            let mut prod: f64 = 1.0;
            for arg in args {
                prod *= to_float(arg)?;
            }
            Ok(KlujurVal::float(prod))
        }
        PromotingCategory::BigRatio => {
            let mut num = BigInt::from(1);
            let mut den = BigInt::from(1);
            for arg in args {
                let (n, d) = to_bigratio(arg)?;
                num = &num * &n;
                den = &den * &d;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        PromotingCategory::BigInt => {
            let mut prod = BigInt::from(1);
            for arg in args {
                prod *= to_bigint(arg)?;
            }
            Ok(KlujurVal::bigint(prod))
        }
    }
}

pub(crate) fn builtin_div(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // 1/x - returns ratio for int, float for float
        return match &args[0] {
            KlujurVal::Int(0) => Err(Error::DivisionByZero),
            KlujurVal::Int(n) => Ok(KlujurVal::ratio(1, *n)),
            KlujurVal::BigInt(n) if n.is_zero() => Err(Error::DivisionByZero),
            KlujurVal::BigInt(n) => Ok(KlujurVal::bigratio(BigInt::from(1), n.clone())),
            KlujurVal::Float(n) => Ok(KlujurVal::float(1.0 / n)),
            KlujurVal::Ratio(num, den) => {
                if *num == 0 {
                    return Err(Error::DivisionByZero);
                }
                Ok(KlujurVal::ratio(*den, *num))
            }
            KlujurVal::BigRatio(num, den) => {
                if num.is_zero() {
                    return Err(Error::DivisionByZero);
                }
                Ok(KlujurVal::bigratio(den.clone(), num.clone()))
            }
            other => Err(Error::type_error_in("/", "number", other.type_name())),
        };
    }

    // Division uses rational arithmetic: Float -> Float, otherwise BigRatio or i64 Ratio
    match classify_numeric_args(args)? {
        NumericCategory::Float => {
            let mut result = to_float(&args[0])?;
            for arg in &args[1..] {
                let divisor = to_float(arg)?;
                result /= divisor;
            }
            Ok(KlujurVal::float(result))
        }
        // For division, BigInt/BigRatio/Ratio all use BigRatio arithmetic
        NumericCategory::BigRatio | NumericCategory::BigInt | NumericCategory::Ratio => {
            let (mut num, mut den) = to_bigratio(&args[0])?;
            for arg in &args[1..] {
                let (n, d) = to_bigratio(arg)?;
                if n.is_zero() {
                    return Err(Error::DivisionByZero);
                }
                // (num/den) / (n/d) = (num*d) / (den*n)
                num = &num * &d;
                den = &den * &n;
            }
            Ok(KlujurVal::bigratio(num, den))
        }
        // All integers (i64) - produces an i64 ratio
        NumericCategory::Int => {
            let (mut num, mut den) = to_i64_ratio(&args[0])?;
            for arg in &args[1..] {
                let (n, d) = to_i64_ratio(arg)?;
                if n == 0 {
                    return Err(Error::DivisionByZero);
                }
                // (num/den) / (n/d) = (num*d) / (den*n)
                num = num
                    .checked_mul(d)
                    .ok_or(Error::IntegerOverflow { operation: "/" })?;
                den = den
                    .checked_mul(n)
                    .ok_or(Error::IntegerOverflow { operation: "/" })?;
            }
            Ok(KlujurVal::ratio(num, den))
        }
    }
}

pub(crate) fn builtin_quot(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.len() != 2 {
        return Err(Error::arity_named("quot", 2, args.len()));
    }

    match (&args[0], &args[1]) {
        (KlujurVal::Int(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::Int(b)) => Ok(KlujurVal::int(a / b)),
        (KlujurVal::Int(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::BigInt(b)) => Ok(KlujurVal::bigint(BigInt::from(*a) / b)),
        (KlujurVal::BigInt(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::Int(b)) => Ok(KlujurVal::bigint(a / BigInt::from(*b))),
        (KlujurVal::BigInt(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::BigInt(b)) => Ok(KlujurVal::bigint(a / b)),
        (other, _) => Err(Error::type_error_in("quot", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_rem(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.len() != 2 {
        return Err(Error::arity_named("rem", 2, args.len()));
    }

    match (&args[0], &args[1]) {
        (KlujurVal::Int(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::Int(b)) => Ok(KlujurVal::int(a % b)),
        (KlujurVal::Int(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::BigInt(b)) => Ok(KlujurVal::bigint(BigInt::from(*a) % b)),
        (KlujurVal::BigInt(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::Int(b)) => Ok(KlujurVal::bigint(a % BigInt::from(*b))),
        (KlujurVal::BigInt(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::BigInt(b)) => Ok(KlujurVal::bigint(a % b)),
        (other, _) => Err(Error::type_error_in("rem", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_mod(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::{Signed, Zero};

    if args.len() != 2 {
        return Err(Error::arity_named("mod", 2, args.len()));
    }

    match (&args[0], &args[1]) {
        (KlujurVal::Int(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::Int(b)) => {
            // Clojure's mod: result has same sign as divisor
            let rem = a % b;
            if (rem < 0 && *b > 0) || (rem > 0 && *b < 0) {
                Ok(KlujurVal::int(rem + b))
            } else {
                Ok(KlujurVal::int(rem))
            }
        }
        (KlujurVal::Int(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::Int(a), KlujurVal::BigInt(b)) => {
            let a_big = BigInt::from(*a);
            let rem = &a_big % b;
            if (rem.is_negative() && b.is_positive()) || (rem.is_positive() && b.is_negative()) {
                Ok(KlujurVal::bigint(&rem + b))
            } else {
                Ok(KlujurVal::bigint(rem))
            }
        }
        (KlujurVal::BigInt(_), KlujurVal::Int(0)) => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::Int(b)) => {
            let b_big = BigInt::from(*b);
            let rem = a % &b_big;
            if (rem.is_negative() && *b > 0) || (rem.is_positive() && *b < 0) {
                Ok(KlujurVal::bigint(&rem + &b_big))
            } else {
                Ok(KlujurVal::bigint(rem))
            }
        }
        (KlujurVal::BigInt(_), KlujurVal::BigInt(b)) if b.is_zero() => Err(Error::DivisionByZero),
        (KlujurVal::BigInt(a), KlujurVal::BigInt(b)) => {
            let rem = a % b;
            if (rem.is_negative() && b.is_positive()) || (rem.is_positive() && b.is_negative()) {
                Ok(KlujurVal::bigint(&rem + b))
            } else {
                Ok(KlujurVal::bigint(rem))
            }
        }
        (other, _) => Err(Error::type_error_in("mod", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_inc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("inc", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(
            n.checked_add(1)
                .ok_or(Error::IntegerOverflow { operation: "inc" })?,
        )),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(n + 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n + 1.0)),
        other => Err(Error::type_error_in("inc", "number", other.type_name())),
    }
}

/// Auto-promoting increment that promotes to BigInt on overflow.
pub(crate) fn builtin_inc_prime(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("inc'", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bigint(BigInt::from(*n) + 1)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(n + 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n + 1.0)),
        other => Err(Error::type_error_in("inc'", "number", other.type_name())),
    }
}

pub(crate) fn builtin_dec(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("dec", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(
            n.checked_sub(1)
                .ok_or(Error::IntegerOverflow { operation: "dec" })?,
        )),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(n - 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n - 1.0)),
        other => Err(Error::type_error_in("dec", "number", other.type_name())),
    }
}

/// Auto-promoting decrement that promotes to BigInt on overflow.
pub(crate) fn builtin_dec_prime(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("dec'", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bigint(BigInt::from(*n) - 1)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(n - 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n - 1.0)),
        other => Err(Error::type_error_in("dec'", "number", other.type_name())),
    }
}

pub(crate) fn builtin_max(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let mut max = args[0].clone();
    for arg in &args[1..] {
        if compare_numbers(arg, &max)? == std::cmp::Ordering::Greater {
            max = arg.clone();
        }
    }
    Ok(max)
}

pub(crate) fn builtin_min(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let mut min = args[0].clone();
    for arg in &args[1..] {
        if compare_numbers(arg, &min)? == std::cmp::Ordering::Less {
            min = arg.clone();
        }
    }
    Ok(min)
}

pub(crate) fn builtin_abs(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Signed;

    if args.len() != 1 {
        return Err(Error::arity_named("abs", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(
            n.checked_abs()
                .ok_or(Error::IntegerOverflow { operation: "abs" })?,
        )),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bigint(n.abs())),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n.abs())),
        KlujurVal::Ratio(num, den) => {
            let abs_num = num
                .checked_abs()
                .ok_or(Error::IntegerOverflow { operation: "abs" })?;
            Ok(KlujurVal::ratio(abs_num, *den))
        }
        KlujurVal::BigRatio(num, den) => Ok(KlujurVal::bigratio(num.abs(), den.clone())),
        other => Err(Error::type_error_in("abs", "number", other.type_name())),
    }
}

pub(crate) fn builtin_double(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("double", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::float(*n as f64)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::float(n.to_f64().unwrap_or(f64::INFINITY))),
        KlujurVal::Float(n) => Ok(KlujurVal::float(*n)),
        KlujurVal::Ratio(num, den) => Ok(KlujurVal::float(*num as f64 / *den as f64)),
        KlujurVal::BigRatio(num, den) => {
            let nf = num.to_f64().unwrap_or(f64::INFINITY);
            let df = den.to_f64().unwrap_or(f64::INFINITY);
            Ok(KlujurVal::float(nf / df))
        }
        other => Err(Error::type_error_in("double", "number", other.type_name())),
    }
}

pub(crate) fn builtin_int(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("int", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(*n)),
        KlujurVal::BigInt(n) => {
            // Try to convert to i64, error if out of range
            n.to_i64()
                .map(KlujurVal::int)
                .ok_or_else(|| Error::EvalError("BigInt too large for int".into()))
        }
        KlujurVal::Float(n) => Ok(KlujurVal::int(*n as i64)),
        KlujurVal::Ratio(num, den) => {
            // Truncate towards zero, like Clojure's int
            Ok(KlujurVal::int(*num / *den))
        }
        KlujurVal::BigRatio(num, den) => {
            // Truncate towards zero
            let result = num / den;
            result
                .to_i64()
                .map(KlujurVal::int)
                .ok_or_else(|| Error::EvalError("BigRatio too large for int".into()))
        }
        other => Err(Error::type_error_in("int", "number", other.type_name())),
    }
}

// ============================================================================
// Numeric Predicates
// ============================================================================

pub(crate) fn builtin_even_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.len() != 1 {
        return Err(Error::arity_named("even?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 == 0)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bool((n % BigInt::from(2)).is_zero())),
        other => Err(Error::type_error_in("even?", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_odd_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.len() != 1 {
        return Err(Error::arity_named("odd?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 != 0)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bool(!(n % BigInt::from(2)).is_zero())),
        other => Err(Error::type_error_in("odd?", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_pos_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Signed;

    if args.len() != 1 {
        return Err(Error::arity_named("pos?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n > 0)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bool(n.is_positive())),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n > 0.0)),
        KlujurVal::Ratio(num, _) => Ok(KlujurVal::bool(*num > 0)),
        KlujurVal::BigRatio(num, _) => Ok(KlujurVal::bool(num.is_positive())),
        other => Err(Error::type_error_in("pos?", "number", other.type_name())),
    }
}

pub(crate) fn builtin_neg_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Signed;

    if args.len() != 1 {
        return Err(Error::arity_named("neg?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n < 0)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bool(n.is_negative())),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n < 0.0)),
        KlujurVal::Ratio(num, _) => Ok(KlujurVal::bool(*num < 0)),
        KlujurVal::BigRatio(num, _) => Ok(KlujurVal::bool(num.is_negative())),
        other => Err(Error::type_error_in("neg?", "number", other.type_name())),
    }
}

pub(crate) fn builtin_zero_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use num_traits::Zero;

    if args.len() != 1 {
        return Err(Error::arity_named("zero?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n == 0)),
        KlujurVal::BigInt(n) => Ok(KlujurVal::bool(n.is_zero())),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n == 0.0)),
        KlujurVal::Ratio(num, _) => Ok(KlujurVal::bool(*num == 0)),
        KlujurVal::BigRatio(num, _) => Ok(KlujurVal::bool(num.is_zero())),
        other => Err(Error::type_error_in("zero?", "number", other.type_name())),
    }
}
