// klujur-core - Common test utilities
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Shared test helpers and utilities for Klujur integration tests.
//!
//! # Usage
//!
//! In your test file, add:
//! ```ignore
//! mod common;
//! use common::*;
//! ```
//!
//! # Available Helpers
//!
//! - [`eval_str`] - Evaluate code in a fresh environment with builtins
//! - [`eval_str_with_env`] - Evaluate code in an existing environment
//! - [`eval_str_with_stdlib`] - Evaluate code with full standard library
//! - [`eval_all`] - Evaluate multiple expressions, returning the last
//! - [`new_env`] - Create a new environment with builtins registered
//! - [`new_env_with_stdlib`] - Create a new environment with full stdlib
//!
//! # Macros
//!
//! - [`assert_eval!`] - Assert that code evaluates to an expected value
//! - [`assert_eval_err!`] - Assert that code produces an error
//! - [`assert_eval_with_env!`] - Assert evaluation with a shared environment

// Re-export common types for convenience
pub use klujur_core::builtins::register_builtins;
pub use klujur_core::env::Env;
pub use klujur_core::eval::eval;
pub use klujur_core::init_stdlib;
#[allow(unused_imports)]
pub use klujur_parser::{Keyword, KlujurVal, Parser};

/// Evaluate a Klujur expression string in a fresh environment.
///
/// The environment is pre-populated with built-in functions but not the
/// standard library (use [`eval_str_with_stdlib`] for that).
///
/// # Returns
///
/// Returns the evaluated value, or an error message string.
#[must_use]
pub fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_str_with_env(s, &env)
}

/// Evaluate a Klujur expression string in the given environment.
///
/// # Returns
///
/// Returns the evaluated value, or an error message string.
#[must_use]
pub fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

/// Evaluate a Klujur expression string with the full standard library loaded.
///
/// This is slower than [`eval_str`] but provides access to all standard
/// library functions and macros (defn, let, cond, ->, etc.).
///
/// # Returns
///
/// Returns the evaluated value, or an error message string.
#[must_use]
#[allow(dead_code)]
pub fn eval_str_with_stdlib(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).map_err(|e| e.to_string())?;
    eval_str_with_env(s, &env)
}

/// Evaluate multiple Klujur expressions, returning the last result.
///
/// This is useful when you need to set up definitions before the final
/// expression. Each expression is parsed and evaluated sequentially.
///
/// # Returns
///
/// Returns the value of the last expression, or an error.
#[must_use]
pub fn eval_all(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    let mut result = KlujurVal::Nil;

    while let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
        result = eval(&expr, env).map_err(|e| e.to_string())?;
    }

    Ok(result)
}

/// Create a new environment with builtins registered.
///
/// # Returns
///
/// A fresh [`Env`] with all built-in functions available.
#[must_use]
pub fn new_env() -> Env {
    let env = Env::new();
    register_builtins(&env);
    env
}

/// Create a new environment with the full standard library loaded.
///
/// # Panics
///
/// Panics if the standard library fails to load (should never happen).
#[must_use]
#[allow(dead_code)]
pub fn new_env_with_stdlib() -> Env {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).expect("Failed to load standard library");
    env
}

/// Evaluate multiple Klujur expressions with stdlib, returning the last result.
///
/// This is useful for tests that need stdlib macros and need to set up
/// definitions before the final expression. Each string can contain multiple
/// expressions which are parsed and evaluated sequentially.
///
/// # Returns
///
/// Returns the value of the last expression, or an error.
#[must_use]
#[allow(dead_code)]
pub fn eval_all_with_stdlib(strs: &[&str]) -> Result<KlujurVal, String> {
    let env = new_env_with_stdlib();
    let mut result = KlujurVal::Nil;
    for s in strs {
        result = eval_all(s, &env)?;
    }
    Ok(result)
}

/// Assert that evaluating `input` produces the expected value.
///
/// # Example
///
/// ```ignore
/// assert_eval!("(+ 1 2)", KlujurVal::int(3));
/// ```
#[macro_export]
macro_rules! assert_eval {
    ($input:expr, $expected:expr) => {
        let result = $crate::common::eval_str($input);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

/// Assert that evaluating `input` produces an error.
///
/// # Example
///
/// ```ignore
/// assert_eval_err!("(+ 1 :not-a-number)");
/// ```
#[macro_export]
macro_rules! assert_eval_err {
    ($input:expr) => {
        let result = $crate::common::eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
    };
}

/// Assert that evaluating `input` in the given environment produces the expected value.
///
/// # Example
///
/// ```ignore
/// let env = new_env();
/// eval_str_with_env("(def x 42)", &env).unwrap();
/// assert_eval_with_env!("x", KlujurVal::int(42), &env);
/// ```
#[macro_export]
macro_rules! assert_eval_with_env {
    ($input:expr, $expected:expr, $env:expr) => {
        let result = $crate::common::eval_str_with_env($input, $env);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

/// Assert that evaluating `input` produces an error matching the given pattern.
///
/// # Example
///
/// ```ignore
/// assert_eval_err_contains!("(/ 1 0)", "divide by zero");
/// ```
#[macro_export]
macro_rules! assert_eval_err_contains {
    ($input:expr, $pattern:expr) => {
        let result = $crate::common::eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.to_lowercase().contains(&$pattern.to_lowercase()),
            "Error message '{}' does not contain '{}'",
            err_msg,
            $pattern
        );
    };
}

/// Assert that evaluating `input` with stdlib produces the expected value.
///
/// This is slower than `assert_eval!` but provides access to all stdlib
/// functions and macros.
///
/// # Example
///
/// ```ignore
/// assert_eval_stdlib!("(-> 1 (+ 2) (* 3))", KlujurVal::int(9));
/// ```
#[macro_export]
macro_rules! assert_eval_stdlib {
    ($input:expr, $expected:expr) => {
        let result = $crate::common::eval_str_with_stdlib($input);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_str_basic() {
        assert_eq!(eval_str("42").unwrap(), KlujurVal::int(42));
        assert_eq!(eval_str("(+ 1 2)").unwrap(), KlujurVal::int(3));
    }

    #[test]
    fn test_eval_str_error() {
        assert!(eval_str("(+ 1 :not-a-number)").is_err());
    }

    #[test]
    fn test_new_env() {
        let env = new_env();
        let result = eval_str_with_env("(+ 1 2)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(3));
    }

    #[test]
    fn test_eval_all() {
        let env = new_env();
        let result = eval_all("(def x 1) (def y 2) (+ x y)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(3));
    }
}
