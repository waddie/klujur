// klujur-core - Mathematical built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Mathematical functions: sqrt, pow, sin, cos, tan, asin, acos, atan, atan2,
//! log, log10, log2, exp, floor, ceil, round, signum

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Helper to extract a number as f64
// ============================================================================

fn to_f64(val: &KlujurVal, fn_name: &str) -> Result<f64> {
    match val {
        KlujurVal::Int(n) => Ok(*n as f64),
        KlujurVal::Float(n) => Ok(*n),
        KlujurVal::Ratio(num, den) => Ok(*num as f64 / *den as f64),
        other => Err(Error::type_error_in(fn_name, "number", other.type_name())),
    }
}

// ============================================================================
// Roots and Powers
// ============================================================================

/// (sqrt n) - square root
pub(crate) fn builtin_sqrt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sqrt", 1, args.len()));
    }
    let n = to_f64(&args[0], "sqrt")?;
    Ok(KlujurVal::float(n.sqrt()))
}

/// (pow base exp) - raise base to the power exp
pub(crate) fn builtin_pow(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("pow", 2, args.len()));
    }
    let base = to_f64(&args[0], "pow")?;
    let exp = to_f64(&args[1], "pow")?;
    Ok(KlujurVal::float(base.powf(exp)))
}

/// (cbrt n) - cube root
pub(crate) fn builtin_cbrt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("cbrt", 1, args.len()));
    }
    let n = to_f64(&args[0], "cbrt")?;
    Ok(KlujurVal::float(n.cbrt()))
}

// ============================================================================
// Trigonometric Functions
// ============================================================================

/// (sin x) - sine of x (radians)
pub(crate) fn builtin_sin(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sin", 1, args.len()));
    }
    let n = to_f64(&args[0], "sin")?;
    Ok(KlujurVal::float(n.sin()))
}

/// (cos x) - cosine of x (radians)
pub(crate) fn builtin_cos(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("cos", 1, args.len()));
    }
    let n = to_f64(&args[0], "cos")?;
    Ok(KlujurVal::float(n.cos()))
}

/// (tan x) - tangent of x (radians)
pub(crate) fn builtin_tan(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("tan", 1, args.len()));
    }
    let n = to_f64(&args[0], "tan")?;
    Ok(KlujurVal::float(n.tan()))
}

/// (asin x) - arc sine, returns radians
pub(crate) fn builtin_asin(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("asin", 1, args.len()));
    }
    let n = to_f64(&args[0], "asin")?;
    Ok(KlujurVal::float(n.asin()))
}

/// (acos x) - arc cosine, returns radians
pub(crate) fn builtin_acos(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("acos", 1, args.len()));
    }
    let n = to_f64(&args[0], "acos")?;
    Ok(KlujurVal::float(n.acos()))
}

/// (atan x) - arc tangent, returns radians
pub(crate) fn builtin_atan(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("atan", 1, args.len()));
    }
    let n = to_f64(&args[0], "atan")?;
    Ok(KlujurVal::float(n.atan()))
}

/// (atan2 y x) - two-argument arc tangent
pub(crate) fn builtin_atan2(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("atan2", 2, args.len()));
    }
    let y = to_f64(&args[0], "atan2")?;
    let x = to_f64(&args[1], "atan2")?;
    Ok(KlujurVal::float(y.atan2(x)))
}

/// (sinh x) - hyperbolic sine
pub(crate) fn builtin_sinh(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sinh", 1, args.len()));
    }
    let n = to_f64(&args[0], "sinh")?;
    Ok(KlujurVal::float(n.sinh()))
}

/// (cosh x) - hyperbolic cosine
pub(crate) fn builtin_cosh(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("cosh", 1, args.len()));
    }
    let n = to_f64(&args[0], "cosh")?;
    Ok(KlujurVal::float(n.cosh()))
}

/// (tanh x) - hyperbolic tangent
pub(crate) fn builtin_tanh(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("tanh", 1, args.len()));
    }
    let n = to_f64(&args[0], "tanh")?;
    Ok(KlujurVal::float(n.tanh()))
}

// ============================================================================
// Logarithms and Exponentials
// ============================================================================

/// (log x) - natural logarithm (base e)
pub(crate) fn builtin_log(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("log", 1, args.len()));
    }
    let n = to_f64(&args[0], "log")?;
    Ok(KlujurVal::float(n.ln()))
}

/// (log10 x) - base-10 logarithm
pub(crate) fn builtin_log10(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("log10", 1, args.len()));
    }
    let n = to_f64(&args[0], "log10")?;
    Ok(KlujurVal::float(n.log10()))
}

/// (log2 x) - base-2 logarithm
pub(crate) fn builtin_log2(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("log2", 1, args.len()));
    }
    let n = to_f64(&args[0], "log2")?;
    Ok(KlujurVal::float(n.log2()))
}

/// (exp x) - e raised to the power x
pub(crate) fn builtin_exp(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("exp", 1, args.len()));
    }
    let n = to_f64(&args[0], "exp")?;
    Ok(KlujurVal::float(n.exp()))
}

// ============================================================================
// Rounding
// ============================================================================

/// (floor x) - largest integer not greater than x
pub(crate) fn builtin_floor(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("floor", 1, args.len()));
    }
    let n = to_f64(&args[0], "floor")?;
    Ok(KlujurVal::float(n.floor()))
}

/// (ceil x) - smallest integer not less than x
pub(crate) fn builtin_ceil(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ceil", 1, args.len()));
    }
    let n = to_f64(&args[0], "ceil")?;
    Ok(KlujurVal::float(n.ceil()))
}

/// (round x) - round to nearest integer (half up)
pub(crate) fn builtin_round(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("round", 1, args.len()));
    }
    let n = to_f64(&args[0], "round")?;
    Ok(KlujurVal::float(n.round()))
}

/// (trunc x) - truncate toward zero
pub(crate) fn builtin_trunc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("trunc", 1, args.len()));
    }
    let n = to_f64(&args[0], "trunc")?;
    Ok(KlujurVal::float(n.trunc()))
}

// ============================================================================
// Miscellaneous
// ============================================================================

/// (signum x) - sign of x: -1, 0, or 1
pub(crate) fn builtin_signum(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("signum", 1, args.len()));
    }
    let n = to_f64(&args[0], "signum")?;
    Ok(KlujurVal::float(n.signum()))
}

/// (hypot x y) - sqrt(x^2 + y^2) without overflow
pub(crate) fn builtin_hypot(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("hypot", 2, args.len()));
    }
    let x = to_f64(&args[0], "hypot")?;
    let y = to_f64(&args[1], "hypot")?;
    Ok(KlujurVal::float(x.hypot(y)))
}

/// (nan? x) - true if x is NaN
pub(crate) fn builtin_nan_q(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nan?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Float(n) => Ok(KlujurVal::Bool(n.is_nan())),
        KlujurVal::Int(_) => Ok(KlujurVal::Bool(false)),
        other => Err(Error::type_error_in("nan?", "number", other.type_name())),
    }
}

/// (infinite? x) - true if x is infinite
pub(crate) fn builtin_infinite_q(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("infinite?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Float(n) => Ok(KlujurVal::Bool(n.is_infinite())),
        KlujurVal::Int(_) => Ok(KlujurVal::Bool(false)),
        other => Err(Error::type_error_in(
            "infinite?",
            "number",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Constants
// ============================================================================

/// (pi) - the constant pi
pub(crate) fn builtin_pi(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("pi", 0, args.len()));
    }
    Ok(KlujurVal::float(std::f64::consts::PI))
}

/// (e) - the constant e (Euler's number)
pub(crate) fn builtin_e(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("e", 0, args.len()));
    }
    Ok(KlujurVal::float(std::f64::consts::E))
}

/// (to-radians deg) - convert degrees to radians
pub(crate) fn builtin_to_radians(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("to-radians", 1, args.len()));
    }
    let deg = to_f64(&args[0], "to-radians")?;
    Ok(KlujurVal::float(deg.to_radians()))
}

/// (to-degrees rad) - convert radians to degrees
pub(crate) fn builtin_to_degrees(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("to-degrees", 1, args.len()));
    }
    let rad = to_f64(&args[0], "to-degrees")?;
    Ok(KlujurVal::float(rad.to_degrees()))
}
