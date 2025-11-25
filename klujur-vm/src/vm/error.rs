// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Runtime errors for the VM.

/// Runtime error during VM execution.
#[derive(Debug, Clone)]
pub enum RuntimeError {
    /// Stack underflow.
    StackUnderflow,
    /// Type error.
    TypeError { expected: String, got: String },
    /// Division by zero.
    DivisionByZero,
    /// Undefined variable.
    UndefinedVariable(String),
    /// Not callable.
    NotCallable(String),
    /// Wrong number of arguments.
    ArityError { expected: usize, got: usize },
    /// Internal error.
    Internal(String),
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::StackUnderflow => write!(f, "Stack underflow"),
            RuntimeError::TypeError { expected, got } => {
                write!(f, "Type error: expected {}, got {}", expected, got)
            }
            RuntimeError::DivisionByZero => write!(f, "Division by zero"),
            RuntimeError::UndefinedVariable(name) => write!(f, "Undefined variable: {}", name),
            RuntimeError::NotCallable(typ) => write!(f, "Value is not callable: {}", typ),
            RuntimeError::ArityError { expected, got } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {}, got {}",
                    expected, got
                )
            }
            RuntimeError::Internal(msg) => write!(f, "Internal error: {}", msg),
        }
    }
}

impl std::error::Error for RuntimeError {}

/// Result type for VM operations.
pub type Result<T> = std::result::Result<T, RuntimeError>;
