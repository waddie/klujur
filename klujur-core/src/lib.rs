// klujur-core - Runtime and evaluator for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! # klujur-core
//!
//! Runtime and evaluator for the Klujur programming language.
//! Provides an AST-walking interpreter for `KlujurVal` expressions.

pub mod bindings;
pub mod builtins;
pub mod env;
pub mod error;
pub mod eval;
pub mod namespace;

pub use bindings::{deref_var, get_thread_binding, has_thread_binding, push_bindings};
pub use builtins::register_builtins;
pub use env::Env;
pub use error::{Error, Result};
pub use eval::{apply, eval, make_native_fn};
pub use namespace::{Namespace, NamespaceRegistry};

// Re-export parser types for convenience
pub use klujur_parser::{Keyword, KlujurVal, Symbol};

/// Embedded standard library source (macros and utility functions).
const CORE_STDLIB: &str = include_str!("../../klujur-std/core.cljc");

/// Initialise the standard library by evaluating embedded macros.
///
/// Call this after `register_builtins` to load standard macros like
/// `if-let`, `when-let`, `case`, `condp`, `dotimes`, `doseq`, etc.
pub fn init_stdlib(env: &Env) -> Result<()> {
    let mut parser = klujur_parser::Parser::new(CORE_STDLIB)
        .map_err(|e| Error::EvalError(format!("Failed to parse stdlib: {:?}", e)))?;

    while let Some(expr) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("Failed to parse stdlib: {:?}", e)))?
    {
        eval::eval(&expr, env)?;
    }

    Ok(())
}
