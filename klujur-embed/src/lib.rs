// klujur-embed - Embedding API for Klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! # klujur-embed
//!
//! A high-level embedding API for the Klujur programming language.
//!
//! This crate provides a simple, ergonomic interface for embedding Klujur
//! in Rust applications. It handles environment setup, type conversion,
//! and function registration.
//!
//! ## Quick Start
//!
//! ```rust
//! use klujur_embed::Engine;
//!
//! let engine = Engine::new().unwrap();
//! let result = engine.eval("(+ 1 2 3)").unwrap();
//! println!("{}", result); // 6
//! ```
//!
//! ## Registering Native Functions
//!
//! ```rust
//! use klujur_embed::{Engine, KlujurVal, Result};
//!
//! let engine = Engine::new().unwrap();
//! engine.register_native("double", |args: &[KlujurVal]| -> Result<KlujurVal> {
//!     match args.first() {
//!         Some(KlujurVal::Int(n)) => Ok(KlujurVal::int(n * 2)),
//!         _ => Err(klujur_embed::Error::type_error("integer", "other")),
//!     }
//! });
//! let result = engine.eval("(double 21)").unwrap();
//! assert_eq!(result.to_string(), "42");
//! ```

mod convert;
mod engine;

pub use convert::{FromKlujurVal, IntoKlujurVal, from_klujur, to_klujur};
pub use engine::Engine;

// Re-export core types for convenience
pub use klujur_core::{Error, Result};
pub use klujur_parser::{CustomType, KlujurCustom, KlujurVal};
