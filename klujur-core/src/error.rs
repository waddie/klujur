// klujur-core - Error types for the Klujur evaluator
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Error types for Klujur evaluation.
//!
//! # Examples
//!
//! ```
//! use klujur_core::{Error, Result};
//!
//! // Create typed errors
//! let arity_err = Error::arity_named("my-fn", 2, 3);
//! assert!(arity_err.to_string().contains("my-fn"));
//! assert!(arity_err.to_string().contains("expected 2"));
//!
//! let type_err = Error::type_error("integer", "string");
//! assert!(type_err.to_string().contains("expected integer"));
//! ```

use klujur_parser::{KlujurVal, Symbol};
use std::fmt;

/// Result type for Klujur evaluation.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during evaluation.
///
/// # Examples
///
/// ```
/// use klujur_core::Error;
///
/// // Arity errors include function name and expected/actual counts
/// let err = Error::arity_named("inc", 1, 0);
/// assert_eq!(
///     err.to_string(),
///     "Wrong number of arguments to 'inc': expected 1, got 0"
/// );
///
/// // Type errors show expected vs actual types
/// let err = Error::type_error("number", "string");
/// assert_eq!(
///     err.to_string(),
///     "Type error: expected number, got string"
/// );
/// ```
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
    /// Integer overflow
    IntegerOverflow { operation: &'static str },
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
    /// I/O error (file operations, etc.)
    IoError {
        operation: &'static str,
        path: Option<String>,
        message: String,
    },
    /// Namespace not found
    NamespaceNotFound(String),
    /// Protocol not found
    ProtocolNotFound(String),
    /// Symbol is not public in its namespace
    NotPublic { symbol: String, namespace: String },
    /// Missing required field in record construction
    MissingField { record: String, field: String },
    /// Parse error from the parser
    ParseError(String),
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
            Error::IntegerOverflow { operation } => {
                write!(f, "Integer overflow in '{}'", operation)
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
                write!(f, "Uncaught exception: {}", val)
            }
            Error::Internal(msg) => {
                write!(f, "Internal error: {}", msg)
            }
            Error::IoError {
                operation,
                path,
                message,
            } => {
                if let Some(path) = path {
                    write!(f, "{} '{}': {}", operation, path, message)
                } else {
                    write!(f, "{}: {}", operation, message)
                }
            }
            Error::NamespaceNotFound(ns) => {
                write!(f, "No namespace: {}", ns)
            }
            Error::ProtocolNotFound(proto) => {
                write!(f, "Protocol not found: {}", proto)
            }
            Error::NotPublic { symbol, namespace } => {
                write!(f, "{}/{} is not public", namespace, symbol)
            }
            Error::MissingField { record, field } => {
                write!(
                    f,
                    "Missing required field '{}' for record {}",
                    field, record
                )
            }
            Error::ParseError(msg) => {
                write!(f, "Parse error: {}", msg)
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

    /// Create an arity error for a range (min to max).
    pub fn arity_range(name: impl Into<String>, min: usize, max: usize, got: usize) -> Self {
        Error::ArityError {
            expected: AritySpec::Range(min, max),
            got,
            name: Some(name.into()),
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

    /// Create an I/O error from a std::io::Error.
    pub fn io(operation: &'static str, path: Option<String>, error: std::io::Error) -> Self {
        Error::IoError {
            operation,
            path,
            message: error.to_string(),
        }
    }

    /// Create an I/O error with a custom message.
    pub fn io_msg(
        operation: &'static str,
        path: Option<String>,
        message: impl Into<String>,
    ) -> Self {
        Error::IoError {
            operation,
            path,
            message: message.into(),
        }
    }

    /// Create a namespace not found error.
    pub fn namespace_not_found(ns: impl Into<String>) -> Self {
        Error::NamespaceNotFound(ns.into())
    }

    /// Create a protocol not found error.
    pub fn protocol_not_found(proto: impl Into<String>) -> Self {
        Error::ProtocolNotFound(proto.into())
    }

    /// Create a not public error.
    pub fn not_public(symbol: impl Into<String>, namespace: impl Into<String>) -> Self {
        Error::NotPublic {
            symbol: symbol.into(),
            namespace: namespace.into(),
        }
    }

    /// Create a missing field error.
    pub fn missing_field(record: impl Into<String>, field: impl Into<String>) -> Self {
        Error::MissingField {
            record: record.into(),
            field: field.into(),
        }
    }

    /// Create a parse error.
    pub fn parse_error(message: impl Into<String>) -> Self {
        Error::ParseError(message.into())
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
