// klujur-core - Error types for the Klujur evaluator
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Error types for Klujur evaluation.

use klujur_parser::{KlujurVal, Symbol};
use std::fmt;

/// Result type for Klujur evaluation.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during evaluation.
#[derive(Debug, Clone)]
pub enum Error {
    /// Undefined symbol reference
    UndefinedSymbol(Symbol),
    /// Wrong number of arguments to a function
    ArityError {
        expected: AritySpec,
        got: usize,
        name: Option<String>,
    },
    /// Type error - wrong type for an operation
    TypeError {
        expected: &'static str,
        got: &'static str,
        context: Option<String>,
    },
    /// Attempted to call something that isn't callable
    NotCallable(String),
    /// Division by zero
    DivisionByZero,
    /// Index out of bounds
    IndexOutOfBounds { index: i64, length: usize },
    /// Invalid special form syntax
    InvalidSyntax { form: &'static str, message: String },
    /// General evaluation error
    EvalError(String),
    /// Recur control flow (not a real error, used for tail recursion)
    Recur(Vec<KlujurVal>),
    /// Recur used outside of loop/fn context
    RecurOutsideLoop,
    /// User-thrown exception (via throw)
    Thrown(KlujurVal),
    /// Internal error - invariant violation
    Internal(String),
}

/// Specification for expected arity.
#[derive(Debug, Clone)]
pub enum AritySpec {
    Exact(usize),
    AtLeast(usize),
    Range(usize, usize),
}

impl fmt::Display for AritySpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AritySpec::Exact(n) => write!(f, "{}", n),
            AritySpec::AtLeast(n) => write!(f, "at least {}", n),
            AritySpec::Range(min, max) => write!(f, "{} to {}", min, max),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::UndefinedSymbol(sym) => {
                write!(f, "Unable to resolve symbol: {}", sym)
            }
            Error::ArityError {
                expected,
                got,
                name,
            } => {
                if let Some(name) = name {
                    write!(
                        f,
                        "Wrong number of arguments to '{}': expected {}, got {}",
                        name, expected, got
                    )
                } else {
                    write!(
                        f,
                        "Wrong number of arguments: expected {}, got {}",
                        expected, got
                    )
                }
            }
            Error::TypeError {
                expected,
                got,
                context,
            } => {
                if let Some(ctx) = context {
                    write!(f, "{}: expected {}, got {}", ctx, expected, got)
                } else {
                    write!(f, "Type error: expected {}, got {}", expected, got)
                }
            }
            Error::NotCallable(val) => {
                write!(f, "Cannot call value: {}", val)
            }
            Error::DivisionByZero => {
                write!(f, "Division by zero")
            }
            Error::IndexOutOfBounds { index, length } => {
                write!(
                    f,
                    "Index {} out of bounds for collection of length {}",
                    index, length
                )
            }
            Error::InvalidSyntax { form, message } => {
                write!(f, "Invalid '{}' syntax: {}", form, message)
            }
            Error::EvalError(msg) => {
                write!(f, "{}", msg)
            }
            Error::Recur(_) => {
                write!(f, "recur used outside of loop or fn context")
            }
            Error::RecurOutsideLoop => {
                write!(f, "recur can only be used inside loop or fn")
            }
            Error::Thrown(val) => {
                write!(f, "{}", val)
            }
            Error::Internal(msg) => {
                write!(f, "Internal error: {}", msg)
            }
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// Create an arity error for exact arity.
    pub fn arity(expected: usize, got: usize) -> Self {
        Error::ArityError {
            expected: AritySpec::Exact(expected),
            got,
            name: None,
        }
    }

    /// Create an arity error for exact arity with function name.
    pub fn arity_named(name: impl Into<String>, expected: usize, got: usize) -> Self {
        Error::ArityError {
            expected: AritySpec::Exact(expected),
            got,
            name: Some(name.into()),
        }
    }

    /// Create an arity error for minimum arity.
    pub fn arity_at_least(expected: usize, got: usize) -> Self {
        Error::ArityError {
            expected: AritySpec::AtLeast(expected),
            got,
            name: None,
        }
    }

    /// Create a type error.
    pub fn type_error(expected: &'static str, got: &'static str) -> Self {
        Error::TypeError {
            expected,
            got,
            context: None,
        }
    }

    /// Create a type error with context.
    pub fn type_error_in(
        context: impl Into<String>,
        expected: &'static str,
        got: &'static str,
    ) -> Self {
        Error::TypeError {
            expected,
            got,
            context: Some(context.into()),
        }
    }

    /// Create an invalid syntax error.
    pub fn syntax(form: &'static str, message: impl Into<String>) -> Self {
        Error::InvalidSyntax {
            form,
            message: message.into(),
        }
    }
}

/// Helper to check if a value is a specific type for error messages.
pub fn check_type(val: &KlujurVal, expected: &'static str) -> Result<()> {
    let got = val.type_name();
    if got == expected {
        Ok(())
    } else {
        Err(Error::type_error(expected, got))
    }
}
