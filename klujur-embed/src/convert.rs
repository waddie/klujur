// klujur-embed - Type conversion traits
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Type conversion between Rust and Klujur values.

use std::collections::HashMap;
use std::rc::Rc;

use klujur_core::{Error, Result};
use klujur_parser::KlujurVal;

/// Convert a Rust type into a `KlujurVal`.
pub trait IntoKlujurVal {
    fn into_klujur_val(self) -> KlujurVal;
}

/// Convert a `KlujurVal` into a Rust type.
pub trait FromKlujurVal: Sized {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self>;
}

// ============================================================================
// IntoKlujurVal implementations
// ============================================================================

impl IntoKlujurVal for KlujurVal {
    fn into_klujur_val(self) -> KlujurVal {
        self
    }
}

impl IntoKlujurVal for () {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::Nil
    }
}

impl IntoKlujurVal for bool {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::Bool(self)
    }
}

impl IntoKlujurVal for i64 {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::int(self)
    }
}

impl IntoKlujurVal for i32 {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::int(self as i64)
    }
}

impl IntoKlujurVal for usize {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::int(self as i64)
    }
}

impl IntoKlujurVal for f64 {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::float(self)
    }
}

impl IntoKlujurVal for f32 {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::float(self as f64)
    }
}

impl IntoKlujurVal for char {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::char(self)
    }
}

impl IntoKlujurVal for String {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::string(self)
    }
}

impl IntoKlujurVal for &str {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::string(self)
    }
}

impl IntoKlujurVal for Rc<str> {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::String(self)
    }
}

impl<T: IntoKlujurVal> IntoKlujurVal for Vec<T> {
    fn into_klujur_val(self) -> KlujurVal {
        KlujurVal::vector(self.into_iter().map(|x| x.into_klujur_val()).collect())
    }
}

impl<T: IntoKlujurVal> IntoKlujurVal for Option<T> {
    fn into_klujur_val(self) -> KlujurVal {
        match self {
            Some(v) => v.into_klujur_val(),
            None => KlujurVal::Nil,
        }
    }
}

impl<K: IntoKlujurVal, V: IntoKlujurVal> IntoKlujurVal for HashMap<K, V> {
    fn into_klujur_val(self) -> KlujurVal {
        let pairs: Vec<(KlujurVal, KlujurVal)> = self
            .into_iter()
            .map(|(k, v)| (k.into_klujur_val(), v.into_klujur_val()))
            .collect();
        KlujurVal::map(pairs)
    }
}

// ============================================================================
// FromKlujurVal implementations
// ============================================================================

impl FromKlujurVal for KlujurVal {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        Ok(val.clone())
    }
}

impl FromKlujurVal for () {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Nil => Ok(()),
            other => Err(Error::type_error("nil", other.type_name())),
        }
    }
}

impl FromKlujurVal for bool {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Bool(b) => Ok(*b),
            other => Err(Error::type_error("boolean", other.type_name())),
        }
    }
}

impl FromKlujurVal for i64 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Int(n) => Ok(*n),
            other => Err(Error::type_error("integer", other.type_name())),
        }
    }
}

impl FromKlujurVal for i32 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Int(n) => Ok(*n as i32),
            other => Err(Error::type_error("integer", other.type_name())),
        }
    }
}

impl FromKlujurVal for usize {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Int(n) if *n >= 0 => Ok(*n as usize),
            KlujurVal::Int(_) => Err(Error::type_error(
                "non-negative integer",
                "negative integer",
            )),
            other => Err(Error::type_error("non-negative integer", other.type_name())),
        }
    }
}

impl FromKlujurVal for f64 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Float(n) => Ok(*n),
            KlujurVal::Int(n) => Ok(*n as f64),
            KlujurVal::Ratio(num, den) => Ok(*num as f64 / *den as f64),
            other => Err(Error::type_error("number", other.type_name())),
        }
    }
}

impl FromKlujurVal for f32 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Float(n) => Ok(*n as f32),
            KlujurVal::Int(n) => Ok(*n as f32),
            KlujurVal::Ratio(num, den) => Ok(*num as f32 / *den as f32),
            other => Err(Error::type_error("number", other.type_name())),
        }
    }
}

impl FromKlujurVal for char {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Char(c) => Ok(*c),
            other => Err(Error::type_error("character", other.type_name())),
        }
    }
}

impl FromKlujurVal for String {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::String(s) => Ok(s.to_string()),
            other => Err(Error::type_error("string", other.type_name())),
        }
    }
}

impl<T: FromKlujurVal> FromKlujurVal for Vec<T> {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Vector(v, _) => v.iter().map(|x| T::from_klujur_val(x)).collect(),
            KlujurVal::List(v, _) => v.iter().map(|x| T::from_klujur_val(x)).collect(),
            other => Err(Error::type_error("vector or list", other.type_name())),
        }
    }
}

impl<T: FromKlujurVal> FromKlujurVal for Option<T> {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Nil => Ok(None),
            other => T::from_klujur_val(other).map(Some),
        }
    }
}

// ============================================================================
// Convenience functions
// ============================================================================

/// Convert a Rust value into a KlujurVal.
///
/// This is a convenience function that calls `IntoKlujurVal::into_klujur_val`.
pub fn to_klujur<T: IntoKlujurVal>(value: T) -> KlujurVal {
    value.into_klujur_val()
}

/// Convert a KlujurVal into a Rust type.
///
/// This is a convenience function that calls `FromKlujurVal::from_klujur_val`.
pub fn from_klujur<T: FromKlujurVal>(val: &KlujurVal) -> Result<T> {
    T::from_klujur_val(val)
}
