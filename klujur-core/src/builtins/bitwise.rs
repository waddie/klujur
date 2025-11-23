// klujur-core - Bitwise built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bitwise operations: bit-and, bit-or, bit-xor, bit-not, bit-shift-left, etc.

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Helper
// ============================================================================

/// Helper to get integer for bitwise ops
pub(crate) fn require_int(name: &str, val: &KlujurVal) -> Result<i64> {
    match val {
        KlujurVal::Int(n) => Ok(*n),
        other => Err(Error::type_error_in(name, "integer", other.type_name())),
    }
}

// ============================================================================
// Bitwise Operations
// ============================================================================

/// (bit-and x y & more) - bitwise AND
pub(crate) fn builtin_bit_and(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-and", &args[0])?;
    for arg in &args[1..] {
        result &= require_int("bit-and", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-or x y & more) - bitwise OR
pub(crate) fn builtin_bit_or(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-or", &args[0])?;
    for arg in &args[1..] {
        result |= require_int("bit-or", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-xor x y & more) - bitwise XOR
pub(crate) fn builtin_bit_xor(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-xor", &args[0])?;
    for arg in &args[1..] {
        result ^= require_int("bit-xor", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-not x) - bitwise complement
pub(crate) fn builtin_bit_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("bit-not", 1, args.len()));
    }
    let x = require_int("bit-not", &args[0])?;
    Ok(KlujurVal::int(!x))
}

/// (bit-and-not x y & more) - bitwise AND with complement
pub(crate) fn builtin_bit_and_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-and-not", &args[0])?;
    for arg in &args[1..] {
        result &= !require_int("bit-and-not", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-shift-left x n) - shift left
pub(crate) fn builtin_bit_shift_left(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-shift-left", 2, args.len()));
    }
    let x = require_int("bit-shift-left", &args[0])?;
    let n = require_int("bit-shift-left", &args[1])? as u32;
    Ok(KlujurVal::int(x << n))
}

/// (bit-shift-right x n) - arithmetic shift right
pub(crate) fn builtin_bit_shift_right(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-shift-right", 2, args.len()));
    }
    let x = require_int("bit-shift-right", &args[0])?;
    let n = require_int("bit-shift-right", &args[1])? as u32;
    Ok(KlujurVal::int(x >> n))
}

/// (unsigned-bit-shift-right x n) - logical shift right
pub(crate) fn builtin_unsigned_bit_shift_right(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named(
            "unsigned-bit-shift-right",
            2,
            args.len(),
        ));
    }
    let x = require_int("unsigned-bit-shift-right", &args[0])? as u64;
    let n = require_int("unsigned-bit-shift-right", &args[1])? as u32;
    Ok(KlujurVal::int((x >> n) as i64))
}

/// (bit-set x n) - set bit n
pub(crate) fn builtin_bit_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-set", 2, args.len()));
    }
    let x = require_int("bit-set", &args[0])?;
    let n = require_int("bit-set", &args[1])? as u32;
    Ok(KlujurVal::int(x | (1 << n)))
}

/// (bit-clear x n) - clear bit n
pub(crate) fn builtin_bit_clear(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-clear", 2, args.len()));
    }
    let x = require_int("bit-clear", &args[0])?;
    let n = require_int("bit-clear", &args[1])? as u32;
    Ok(KlujurVal::int(x & !(1 << n)))
}

/// (bit-flip x n) - flip bit n
pub(crate) fn builtin_bit_flip(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-flip", 2, args.len()));
    }
    let x = require_int("bit-flip", &args[0])?;
    let n = require_int("bit-flip", &args[1])? as u32;
    Ok(KlujurVal::int(x ^ (1 << n)))
}

/// (bit-test x n) - test bit n
pub(crate) fn builtin_bit_test(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-test", 2, args.len()));
    }
    let x = require_int("bit-test", &args[0])?;
    let n = require_int("bit-test", &args[1])? as u32;
    Ok(KlujurVal::bool((x >> n) & 1 == 1))
}
