// klujur-core - Runtime and evaluator for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! # klujur-core
//!
//! Runtime and evaluator for the Klujur programming language.
//! Provides an AST-walking interpreter for `KlujurVal` expressions.
//!
//! # Quick Start
//!
//! ```
//! use klujur_core::{Env, eval, register_builtins, init_stdlib};
//! use klujur_parser::Parser;
//!
//! // Set up the environment with builtins and standard library
//! let env = Env::new();
//! register_builtins(&env);
//! init_stdlib(&env).unwrap();
//!
//! // Parse and evaluate an expression
//! let mut parser = Parser::new("(+ 1 2 3)").unwrap();
//! let expr = parser.parse().unwrap().unwrap();
//! let result = eval(&expr, &env).unwrap();
//!
//! assert_eq!(result.to_string(), "6");
//! ```
//!
//! # Core Components
//!
//! - [`Env`] - Lexical environment for variable bindings
//! - [`eval`] - Evaluate a `KlujurVal` expression
//! - [`register_builtins`] - Register native functions
//! - [`init_stdlib`] - Load the standard library macros

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
    apply, eval, get_eval_depth, get_max_eval_depth, is_bytecode_mode, make_native_fn,
    set_bytecode_mode, set_bytecode_registry, set_max_eval_depth,
};
pub use namespace::{Namespace, NamespaceRegistry};

// Re-export parser types for convenience
pub use klujur_parser::{Keyword, KlujurVal, Symbol};

/// Embedded standard library source (macros and utility functions).
const CORE_STDLIB: &str = include_str!("../../klujur-std/core.cljc");

/// Embedded test library source (testing framework).
const TEST_STDLIB: &str = include_str!("../../klujur-std/test.cljc");

/// Initialise the standard library by evaluating embedded macros.
///
/// This loads the standard library into the `klujur.core` namespace,
/// then refers all public vars into the `user` namespace. Call this
/// after `register_builtins`.
///
/// # Examples
///
/// ```
/// use klujur_core::{Env, eval, register_builtins, init_stdlib};
/// use klujur_parser::Parser;
///
/// let env = Env::new();
/// register_builtins(&env);
/// init_stdlib(&env).unwrap();
///
/// // Standard library macros are now available
/// let mut parser = Parser::new("(defn square [x] (* x x))").unwrap();
/// let expr = parser.parse().unwrap().unwrap();
/// eval(&expr, &env).unwrap();
///
/// // Call the defined function
/// let mut parser = Parser::new("(square 5)").unwrap();
/// let expr = parser.parse().unwrap().unwrap();
/// let result = eval(&expr, &env).unwrap();
/// assert_eq!(result.to_string(), "25");
/// ```
pub fn init_stdlib(env: &Env) -> Result<()> {
    let registry = env.registry();

    // Switch to klujur.core namespace to load the stdlib
    registry.set_current(NamespaceRegistry::CORE_NS);

    let mut parser = klujur_parser::Parser::new(CORE_STDLIB)
        .map_err(|e| Error::parse_error(format!("Failed to parse stdlib: {:?}", e)))?;

    while let Some(expr) = parser
        .parse()
        .map_err(|e| Error::parse_error(format!("Failed to parse stdlib: {:?}", e)))?
    {
        eval::eval(&expr, env)?;
    }

    // Register klujur.test as an embedded source (lazy loaded on require)
    registry.register_embedded_source("klujur.test", TEST_STDLIB);

    // Refer all klujur.core publics into the user namespace
    let user_ns = registry.find("user").expect("user namespace should exist");
    registry.refer_core_to(&user_ns);

    // Restore user as the current namespace
    registry.set_current("user");

    Ok(())
}

/// Explicitly initialise the test library.
///
/// This is provided for Rust API users who want to pre-load the test library
/// rather than relying on `(require '[klujur.test])` from Klujur code.
///
/// # Examples
///
/// ```
/// use klujur_core::{Env, register_builtins, init_stdlib, init_test_stdlib};
///
/// let env = Env::new();
/// register_builtins(&env);
/// init_stdlib(&env).unwrap();
/// init_test_stdlib(&env).unwrap();
///
/// // klujur.test is now loaded and ready to use
/// ```
pub fn init_test_stdlib(env: &Env) -> Result<()> {
    let registry = env.registry();
    let prev_ns = registry.current_name();

    // Switch to klujur.test namespace
    registry.set_current("klujur.test");

    let mut parser = klujur_parser::Parser::new(TEST_STDLIB)
        .map_err(|e| Error::parse_error(format!("Failed to parse test lib: {:?}", e)))?;

    while let Some(expr) = parser
        .parse()
        .map_err(|e| Error::parse_error(format!("Failed to parse test lib: {:?}", e)))?
    {
        eval::eval(&expr, env)?;
    }

    registry.mark_loaded("klujur.test");

    // Restore the previous namespace
    registry.set_current(&prev_ns);

    Ok(())
}

/// Realize a value for printing, forcing any lazy sequences.
///
/// In Clojure, printing a lazy sequence forces it. This function
/// recursively walks the value and forces any lazy sequences,
/// converting them to lists for display.
///
/// # Examples
///
/// ```
/// use klujur_core::{Env, eval, register_builtins, init_stdlib, realize_for_print};
/// use klujur_parser::Parser;
///
/// let env = Env::new();
/// register_builtins(&env);
/// init_stdlib(&env).unwrap();
///
/// // Evaluate a lazy sequence
/// let mut parser = Parser::new("(filter even? [1 2 3 4])").unwrap();
/// let expr = parser.parse().unwrap().unwrap();
/// let result = eval(&expr, &env).unwrap();
///
/// // Force and print
/// let realized = realize_for_print(result).unwrap();
/// assert!(realized.to_string().contains("2"));
/// ```
pub fn realize_for_print(val: KlujurVal) -> Result<KlujurVal> {
    use builtins::force_lazy_seq;
    use klujur_parser::{OrdMap, SeqResult};

    match val {
        KlujurVal::LazySeq(ref _ls) => {
            // Force and convert to list
            let mut elements = Vec::new();
            let mut current = val.clone();

            loop {
                match current {
                    KlujurVal::Nil => break,
                    KlujurVal::List(ref items, _) if items.is_empty() => break,
                    KlujurVal::List(ref items, _) => {
                        // Recursively realize elements in case they contain lazy seqs
                        for item in items.iter() {
                            elements.push(realize_for_print(item.clone())?);
                        }
                        break;
                    }
                    KlujurVal::LazySeq(ref ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => break,
                        SeqResult::Cons(first, rest) => {
                            elements.push(realize_for_print(first)?);
                            current = rest;
                        }
                    },
                    other => {
                        elements.push(realize_for_print(other)?);
                        break;
                    }
                }
            }

            Ok(KlujurVal::list(elements))
        }
        // Recursively handle collections that might contain lazy seqs
        KlujurVal::Vector(items, meta) => {
            let realized: Result<Vec<_>> =
                items.iter().map(|v| realize_for_print(v.clone())).collect();
            Ok(KlujurVal::Vector(realized?.into_iter().collect(), meta))
        }
        KlujurVal::List(items, meta) => {
            let realized: Result<Vec<_>> =
                items.iter().map(|v| realize_for_print(v.clone())).collect();
            Ok(KlujurVal::List(realized?.into_iter().collect(), meta))
        }
        KlujurVal::Map(map, meta) => {
            let mut new_map = OrdMap::new();
            for (k, v) in map.iter() {
                new_map.insert(realize_for_print(k.clone())?, realize_for_print(v.clone())?);
            }
            Ok(KlujurVal::Map(new_map, meta))
        }
        // Other values pass through unchanged
        other => Ok(other),
    }
}
