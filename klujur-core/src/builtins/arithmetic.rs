// klujur-core - Arithmetic built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Arithmetic operations: +, -, *, /, quot, rem, mod, inc, dec, max, min, abs

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

use super::compare_numbers;

// ============================================================================
// Arithmetic
// ============================================================================

pub(crate) fn builtin_add(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(0));
    }

    let mut is_float = false;
    let mut int_sum: i64 = 0;
    let mut float_sum: f64 = 0.0;

    for arg in args {
        match arg {
            KlujurVal::Int(n) => {
                if is_float {
                    float_sum += *n as f64;
                } else {
                    int_sum += n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    float_sum = int_sum as f64;
                }
                float_sum += n;
            }
            other => {
                return Err(Error::type_error_in("+", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(float_sum))
    } else {
        Ok(KlujurVal::int(int_sum))
    }
}

pub(crate) fn builtin_sub(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // Unary negation
        return match &args[0] {
            KlujurVal::Int(n) => Ok(KlujurVal::int(-n)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(-n)),
            other => Err(Error::type_error_in("-", "number", other.type_name())),
        };
    }

    let mut is_float = false;
    let mut result: f64 = 0.0;
    let mut int_result: i64 = 0;

    for (i, arg) in args.iter().enumerate() {
        match arg {
            KlujurVal::Int(n) => {
                if i == 0 {
                    if is_float {
                        result = *n as f64;
                    } else {
                        int_result = *n;
                    }
                } else if is_float {
                    result -= *n as f64;
                } else {
                    int_result -= n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    result = int_result as f64;
                }
                if i == 0 {
                    result = *n;
                } else {
                    result -= n;
                }
            }
            other => {
                return Err(Error::type_error_in("-", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(result))
    } else {
        Ok(KlujurVal::int(int_result))
    }
}

pub(crate) fn builtin_mul(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(1));
    }

    let mut is_float = false;
    let mut int_prod: i64 = 1;
    let mut float_prod: f64 = 1.0;

    for arg in args {
        match arg {
            KlujurVal::Int(n) => {
                if is_float {
                    float_prod *= *n as f64;
                } else {
                    int_prod *= n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    float_prod = int_prod as f64;
                }
                float_prod *= n;
            }
            other => {
                return Err(Error::type_error_in("*", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(float_prod))
    } else {
        Ok(KlujurVal::int(int_prod))
    }
}

pub(crate) fn builtin_div(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // 1/x
        return match &args[0] {
            KlujurVal::Int(0) => Err(Error::DivisionByZero),
            KlujurVal::Int(n) => Ok(KlujurVal::float(1.0 / *n as f64)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(1.0 / n)),
            other => Err(Error::type_error_in("/", "number", other.type_name())),
        };
    }

    let mut result = match &args[0] {
        KlujurVal::Int(n) => *n as f64,
        KlujurVal::Float(n) => *n,
        other => return Err(Error::type_error_in("/", "number", other.type_name())),
    };

    for arg in &args[1..] {
        let divisor = match arg {
            KlujurVal::Int(0) => return Err(Error::DivisionByZero),
            KlujurVal::Int(n) => *n as f64,
            KlujurVal::Float(n) => *n,
            other => return Err(Error::type_error_in("/", "number", other.type_name())),
        };
        result /= divisor;
    }

    Ok(KlujurVal::float(result))
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
        KlujurVal::Int(n) => Ok(KlujurVal::int(n + 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n + 1.0)),
        other => Err(Error::type_error_in("inc", "number", other.type_name())),
    }
}

pub(crate) fn builtin_dec(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("dec", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(n - 1)),
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
        KlujurVal::Int(n) => Ok(KlujurVal::int(n.abs())),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n.abs())),
        other => Err(Error::type_error_in("abs", "number", other.type_name())),
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
