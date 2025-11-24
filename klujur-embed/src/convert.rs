// klujur-embed - Type conversion traits
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Type conversion between Rust and Klujur values.
//!
//! This module provides the [`IntoKlujurVal`] and [`FromKlujurVal`] traits for
//! converting between Rust types and [`KlujurVal`].
//!
//! # Built-in Conversions
//!
//! The following types have built-in conversions:
//!
//! | Rust Type | Klujur Type |
//! |-----------|-------------|
//! | `()` | `nil` |
//! | `bool` | `bool` |
//! | `i32`, `i64`, `usize` | `int` |
//! | `f32`, `f64` | `float` |
//! | `char` | `char` |
//! | `String`, `&str` | `string` |
//! | `Vec<T>` | `vector` |
//! | `Option<T>` | `T` or `nil` |
//!
//! # Custom Conversions
//!
//! You can implement these traits for your own types:
//!
//! ```rust
//! use klujur_embed::{IntoKlujurVal, FromKlujurVal, KlujurVal, Result, Error};
//!
//! struct Point { x: i64, y: i64 }
//!
//! impl IntoKlujurVal for Point {
//!     fn into_klujur_val(self) -> KlujurVal {
//!         // Convert to a Klujur vector [x y]
//!         KlujurVal::vector(vec![
//!             KlujurVal::int(self.x),
//!             KlujurVal::int(self.y),
//!         ])
//!     }
//! }
//!
//! impl FromKlujurVal for Point {
//!     fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
//!         match val {
//!             KlujurVal::Vector(v, _) if v.len() == 2 => {
//!                 let x = i64::from_klujur_val(&v[0])?;
//!                 let y = i64::from_klujur_val(&v[1])?;
//!                 Ok(Point { x, y })
//!             }
//!             _ => Err(Error::type_error("vector of 2 ints", val.type_name())),
//!         }
//!     }
//! }
//! ```
//!
//! # HashMap Conversions
//!
//! `HashMap<K, V>` converts to/from Klujur maps:
//!
//! ```rust
//! use std::collections::HashMap;
//! use klujur_embed::{Engine, KlujurVal, FromKlujurVal, IntoKlujurVal};
//!
//! let engine = Engine::new().unwrap();
//!
//! // Rust HashMap -> Klujur map
//! let mut scores: HashMap<String, i64> = HashMap::new();
//! scores.insert("alice".into(), 100);
//! scores.insert("bob".into(), 85);
//! engine.set("scores", scores);
//!
//! // Klujur map -> Rust HashMap
//! engine.eval(r#"(def config {"host" "localhost" "env" "production"})"#).unwrap();
//! let config: HashMap<String, String> = engine.get_as("config").unwrap();
//! assert_eq!(config.get("host"), Some(&"localhost".to_string()));
//! ```
//!
//! # Option Handling
//!
//! `Option<T>` maps to Klujur's nil-punning semantics:
//!
//! ```rust
//! use klujur_embed::{Engine, KlujurVal, FromKlujurVal, IntoKlujurVal};
//!
//! let engine = Engine::new().unwrap();
//!
//! // Some(T) -> T, None -> nil
//! engine.set("present", Some(42i64));  // Sets to 42
//! engine.set("absent", None::<i64>);   // Sets to nil
//!
//! // Klujur nil -> None, value -> Some(T)
//! let present: Option<i64> = engine.get_as("present").unwrap();
//! assert_eq!(present, Some(42));
//!
//! let absent: Option<i64> = engine.get_as("absent").unwrap();
//! assert_eq!(absent, None);
//! ```
//!
//! # Error Handling
//!
//! Conversion errors provide clear type mismatch information:
//!
//! ```rust
//! use klujur_embed::{Engine, KlujurVal, FromKlujurVal};
//!
//! let engine = Engine::new().unwrap();
//! engine.eval(r#"(def name "alice")"#).unwrap();
//!
//! // Type mismatch: string cannot convert to i64
//! let result: Result<Option<i64>, _> = engine.try_get_as("name");
//! assert!(result.is_err());
//!
//! // Use try_get_as to distinguish "not found" from "wrong type"
//! let not_found: Result<Option<i64>, _> = engine.try_get_as("undefined");
//! assert!(not_found.unwrap().is_none());  // Ok(None) = not found
//!
//! let wrong_type: Result<Option<i64>, _> = engine.try_get_as("name");
//! assert!(wrong_type.is_err());  // Err(...) = conversion failed
//! ```

use std::collections::HashMap;
use std::hash::Hash;
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
        use klujur_parser::ToPrimitive;

        match val {
            KlujurVal::Int(n) => Ok(*n),
            KlujurVal::BigInt(n) => n
                .to_i64()
                .ok_or_else(|| Error::EvalError("BigInt too large for i64".into())),
            other => Err(Error::type_error("integer", other.type_name())),
        }
    }
}

impl FromKlujurVal for i32 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Int(n) => {
                if *n < i32::MIN as i64 || *n > i32::MAX as i64 {
                    Err(Error::EvalError(format!(
                        "integer {} out of range for i32 ({}..={})",
                        n,
                        i32::MIN,
                        i32::MAX
                    )))
                } else {
                    Ok(*n as i32)
                }
            }
            other => Err(Error::type_error("integer", other.type_name())),
        }
    }
}

impl FromKlujurVal for usize {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Int(n) if *n >= 0 => {
                // On 32-bit platforms, usize::MAX < i64::MAX, so we need a bounds check
                #[cfg(target_pointer_width = "32")]
                if *n > usize::MAX as i64 {
                    return Err(Error::EvalError(format!(
                        "integer {} out of range for usize (0..={})",
                        n,
                        usize::MAX
                    )));
                }
                Ok(*n as usize)
            }
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
        use klujur_parser::ToPrimitive;

        match val {
            KlujurVal::Float(n) => Ok(*n),
            KlujurVal::Int(n) => Ok(*n as f64),
            KlujurVal::BigInt(n) => Ok(n.to_f64().unwrap_or(f64::INFINITY)),
            KlujurVal::Ratio(num, den) => Ok(*num as f64 / *den as f64),
            KlujurVal::BigRatio(num, den) => {
                let nf = num.to_f64().unwrap_or(f64::INFINITY);
                let df = den.to_f64().unwrap_or(f64::INFINITY);
                Ok(nf / df)
            }
            other => Err(Error::type_error("number", other.type_name())),
        }
    }
}

impl FromKlujurVal for f32 {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Float(n) => {
                let result = *n as f32;
                if result.is_infinite() && n.is_finite() {
                    Err(Error::EvalError(format!("f64 value {} overflows f32", n)))
                } else {
                    Ok(result)
                }
            }
            KlujurVal::Int(n) => Ok(*n as f32),
            KlujurVal::Ratio(num, den) => {
                let result = *num as f32 / *den as f32;
                if result.is_infinite() {
                    Err(Error::EvalError(format!(
                        "ratio {}/{} overflows f32",
                        num, den
                    )))
                } else {
                    Ok(result)
                }
            }
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

impl<K: FromKlujurVal + Eq + Hash, V: FromKlujurVal> FromKlujurVal for HashMap<K, V> {
    fn from_klujur_val(val: &KlujurVal) -> Result<Self> {
        match val {
            KlujurVal::Map(m, _) => {
                let mut result = HashMap::with_capacity(m.len());
                for (k, v) in m.iter() {
                    result.insert(K::from_klujur_val(k)?, V::from_klujur_val(v)?);
                }
                Ok(result)
            }
            other => Err(Error::type_error("map", other.type_name())),
        }
    }
}

// ============================================================================
// Convenience functions
// ============================================================================

/// Convert a Rust value into a KlujurVal.
///
/// This is a convenience function that calls `IntoKlujurVal::into_klujur_val`.
#[must_use]
pub fn to_klujur<T: IntoKlujurVal>(value: T) -> KlujurVal {
    value.into_klujur_val()
}

/// Convert a KlujurVal into a Rust type.
///
/// This is a convenience function that calls `FromKlujurVal::from_klujur_val`.
pub fn from_klujur<T: FromKlujurVal>(val: &KlujurVal) -> Result<T> {
    T::from_klujur_val(val)
}
