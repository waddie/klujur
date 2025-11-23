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
pub use eval::{
    apply, eval, get_eval_depth, get_max_eval_depth, make_native_fn, set_max_eval_depth,
};
pub use namespace::{Namespace, NamespaceRegistry};

// Re-export parser types for convenience
pub use klujur_parser::{Keyword, KlujurVal, Symbol};

/// Embedded standard library source (macros and utility functions).
const CORE_STDLIB: &str = include_str!("../../klujur-std/core.cljc");

/// Initialise the standard library by evaluating embedded macros.
///
/// This loads the standard library into the `klujur.core` namespace,
/// then refers all public vars into the `user` namespace. Call this
/// after `register_builtins`.
pub fn init_stdlib(env: &Env) -> Result<()> {
    let registry = env.registry();

    // Switch to klujur.core namespace to load the stdlib
    registry.set_current(NamespaceRegistry::CORE_NS);

    let mut parser = klujur_parser::Parser::new(CORE_STDLIB)
        .map_err(|e| Error::EvalError(format!("Failed to parse stdlib: {:?}", e)))?;

    while let Some(expr) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("Failed to parse stdlib: {:?}", e)))?
    {
        eval::eval(&expr, env)?;
    }

    // Refer all klujur.core publics into the user namespace
    let user_ns = registry.find("user").expect("user namespace should exist");
    registry.refer_core_to(&user_ns);

    // Restore user as the current namespace
    registry.set_current("user");

    Ok(())
}
