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

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

use super::compare_numbers;

// ============================================================================
// Helper functions for ratio arithmetic
// ============================================================================

/// Convert a numeric value to f64.
fn to_float(val: &KlujurVal) -> Result<f64> {
    match val {
        KlujurVal::Int(n) => Ok(*n as f64),
        KlujurVal::Float(n) => Ok(*n),
        KlujurVal::Ratio(num, den) => Ok(*num as f64 / *den as f64),
        other => Err(Error::type_error_in(
            "arithmetic",
            "number",
            other.type_name(),
        )),
    }
}

/// Convert a numeric value to a ratio (numerator, denominator).
fn to_ratio(val: &KlujurVal) -> Result<(i64, i64)> {
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

// ============================================================================
// Arithmetic
// ============================================================================

pub(crate) fn builtin_add(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(0));
    }

    // Check for floats first (they take precedence)
    let has_float = args.iter().any(|a| matches!(a, KlujurVal::Float(_)));
    if has_float {
        let mut sum: f64 = 0.0;
        for arg in args {
            sum += to_float(arg)?;
        }
        return Ok(KlujurVal::float(sum));
    }

    // Check for ratios
    let has_ratio = args.iter().any(|a| matches!(a, KlujurVal::Ratio(_, _)));
    if has_ratio {
        let mut num: i64 = 0;
        let mut den: i64 = 1;
        for arg in args {
            let (n, d) = to_ratio(arg)?;
            // num/den + n/d = (num*d + n*den) / (den*d)
            num = num
                .checked_mul(d)
                .and_then(|nd| n.checked_mul(den).and_then(|nd2| nd.checked_add(nd2)))
                .ok_or(Error::IntegerOverflow { operation: "+" })?;
            den = den
                .checked_mul(d)
                .ok_or(Error::IntegerOverflow { operation: "+" })?;
        }
        return Ok(KlujurVal::ratio(num, den));
    }

    // All integers
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
            KlujurVal::Float(n) => Ok(KlujurVal::float(-n)),
            KlujurVal::Ratio(num, den) => {
                let neg_num = num
                    .checked_neg()
                    .ok_or(Error::IntegerOverflow { operation: "-" })?;
                Ok(KlujurVal::ratio(neg_num, *den))
            }
            other => Err(Error::type_error_in("-", "number", other.type_name())),
        };
    }

    // Check for floats first (they take precedence)
    let has_float = args.iter().any(|a| matches!(a, KlujurVal::Float(_)));
    if has_float {
        let mut result = to_float(&args[0])?;
        for arg in &args[1..] {
            result -= to_float(arg)?;
        }
        return Ok(KlujurVal::float(result));
    }

    // Check for ratios
    let has_ratio = args.iter().any(|a| matches!(a, KlujurVal::Ratio(_, _)));
    if has_ratio {
        let (mut num, mut den) = to_ratio(&args[0])?;
        for arg in &args[1..] {
            let (n, d) = to_ratio(arg)?;
            // num/den - n/d = (num*d - n*den) / (den*d)
            num = num
                .checked_mul(d)
                .and_then(|nd| n.checked_mul(den).and_then(|nd2| nd.checked_sub(nd2)))
                .ok_or(Error::IntegerOverflow { operation: "-" })?;
            den = den
                .checked_mul(d)
                .ok_or(Error::IntegerOverflow { operation: "-" })?;
        }
        return Ok(KlujurVal::ratio(num, den));
    }

    // All integers
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

pub(crate) fn builtin_mul(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(1));
    }

    // Check for floats first (they take precedence)
    let has_float = args.iter().any(|a| matches!(a, KlujurVal::Float(_)));
    if has_float {
        let mut prod: f64 = 1.0;
        for arg in args {
            prod *= to_float(arg)?;
        }
        return Ok(KlujurVal::float(prod));
    }

    // Check for ratios
    let has_ratio = args.iter().any(|a| matches!(a, KlujurVal::Ratio(_, _)));
    if has_ratio {
        let mut num: i64 = 1;
        let mut den: i64 = 1;
        for arg in args {
            let (n, d) = to_ratio(arg)?;
            // (num/den) * (n/d) = (num*n) / (den*d)
            num = num
                .checked_mul(n)
                .ok_or(Error::IntegerOverflow { operation: "*" })?;
            den = den
                .checked_mul(d)
                .ok_or(Error::IntegerOverflow { operation: "*" })?;
        }
        return Ok(KlujurVal::ratio(num, den));
    }

    // All integers
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

pub(crate) fn builtin_div(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // 1/x - returns ratio for int, float for float
        return match &args[0] {
            KlujurVal::Int(0) => Err(Error::DivisionByZero),
            KlujurVal::Int(n) => Ok(KlujurVal::ratio(1, *n)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(1.0 / n)),
            KlujurVal::Ratio(num, den) => {
                if *num == 0 {
                    return Err(Error::DivisionByZero);
                }
                Ok(KlujurVal::ratio(*den, *num))
            }
            other => Err(Error::type_error_in("/", "number", other.type_name())),
        };
    }

    // Check for floats first (they take precedence)
    let has_float = args.iter().any(|a| matches!(a, KlujurVal::Float(_)));
    if has_float {
        let mut result = to_float(&args[0])?;
        for arg in &args[1..] {
            let divisor = to_float(arg)?;
            result /= divisor;
        }
        return Ok(KlujurVal::float(result));
    }

    // Ratio or integer division - produces a ratio
    let (mut num, mut den) = to_ratio(&args[0])?;
    for arg in &args[1..] {
        let (n, d) = to_ratio(arg)?;
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

pub(crate) fn builtin_quot(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("quot", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("quot", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("quot", "integer", other.type_name())),
    };

    Ok(KlujurVal::int(a / b))
}

pub(crate) fn builtin_rem(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("rem", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("rem", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("rem", "integer", other.type_name())),
    };

    Ok(KlujurVal::int(a % b))
}

pub(crate) fn builtin_mod(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("mod", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("mod", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("mod", "integer", other.type_name())),
    };

    // Clojure's mod: result has same sign as divisor
    let rem = a % b;
    if (rem < 0 && b > 0) || (rem > 0 && b < 0) {
        Ok(KlujurVal::int(rem + b))
    } else {
        Ok(KlujurVal::int(rem))
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
        KlujurVal::Float(n) => Ok(KlujurVal::float(n + 1.0)),
        other => Err(Error::type_error_in("inc", "number", other.type_name())),
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
        KlujurVal::Float(n) => Ok(KlujurVal::float(n - 1.0)),
        other => Err(Error::type_error_in("dec", "number", other.type_name())),
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
    if args.len() != 1 {
        return Err(Error::arity_named("abs", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(
            n.checked_abs()
                .ok_or(Error::IntegerOverflow { operation: "abs" })?,
        )),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n.abs())),
        KlujurVal::Ratio(num, den) => {
            let abs_num = num
                .checked_abs()
                .ok_or(Error::IntegerOverflow { operation: "abs" })?;
            Ok(KlujurVal::ratio(abs_num, *den))
        }
        other => Err(Error::type_error_in("abs", "number", other.type_name())),
    }
}

pub(crate) fn builtin_double(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("double", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::float(*n as f64)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(*n)),
        KlujurVal::Ratio(num, den) => Ok(KlujurVal::float(*num as f64 / *den as f64)),
        other => Err(Error::type_error_in("double", "number", other.type_name())),
    }
}

pub(crate) fn builtin_int(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("int", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(*n)),
        KlujurVal::Float(n) => Ok(KlujurVal::int(*n as i64)),
        KlujurVal::Ratio(num, den) => {
            // Truncate towards zero, like Clojure's int
            Ok(KlujurVal::int(*num / *den))
        }
        other => Err(Error::type_error_in("int", "number", other.type_name())),
    }
}

// ============================================================================
// Numeric Predicates
// ============================================================================

pub(crate) fn builtin_even_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("even?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 == 0)),
        other => Err(Error::type_error_in("even?", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_odd_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("odd?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 != 0)),
        other => Err(Error::type_error_in("odd?", "integer", other.type_name())),
    }
}

pub(crate) fn builtin_pos_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("pos?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n > 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n > 0.0)),
        other => Err(Error::type_error_in("pos?", "number", other.type_name())),
    }
}

pub(crate) fn builtin_neg_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("neg?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n < 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n < 0.0)),
        other => Err(Error::type_error_in("neg?", "number", other.type_name())),
    }
}

pub(crate) fn builtin_zero_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("zero?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n == 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n == 0.0)),
        other => Err(Error::type_error_in("zero?", "number", other.type_name())),
    }
}
