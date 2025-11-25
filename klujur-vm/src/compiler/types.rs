// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Shared types for the bytecode compiler.

use std::collections::{HashMap, HashSet};

use klujur_parser::symbol::Symbol;

/// Error during compilation.
#[derive(Debug, Clone)]
pub enum CompileError {
    /// Constant pool overflow.
    TooManyConstants,
    /// Too many local variables.
    TooManyLocals,
    /// Invalid syntax.
    Syntax(String),
    /// Recur outside loop.
    RecurOutsideLoop,
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::TooManyConstants => write!(f, "Too many constants in function"),
            CompileError::TooManyLocals => write!(f, "Too many local variables"),
            CompileError::Syntax(msg) => write!(f, "Syntax error: {}", msg),
            CompileError::RecurOutsideLoop => write!(f, "recur used outside loop/fn"),
        }
    }
}

impl std::error::Error for CompileError {}

/// Result type for compilation.
pub type Result<T> = std::result::Result<T, CompileError>;

/// Local variable during compilation.
#[derive(Debug, Clone)]
pub struct Local {
    pub name: Symbol,
    pub depth: usize,
    pub is_captured: bool,
    pub is_mutable: bool,
}

/// Information about an upvalue (captured variable).
#[derive(Debug, Clone, Copy)]
pub struct Upvalue {
    /// Index in parent's locals (is_local=true) or parent's upvalues (is_local=false)
    pub index: u16,
    /// True if capturing from parent's locals, false if from parent's upvalues
    pub is_local: bool,
    /// True if this captured variable is mutated via set!
    pub is_mutable: bool,
}

/// Loop context for compiling loop/recur.
#[derive(Debug, Clone)]
pub struct LoopContext {
    /// Jump target for recur.
    pub start_offset: usize,
    /// Stack offsets of loop bindings.
    pub binding_slots: Vec<u16>,
}

/// Enclosing scope information for closure compilation.
pub struct EnclosingScope<'a> {
    /// Parent's locals (for capturing)
    #[allow(dead_code)]
    pub locals: &'a [Local],
    /// Parent's local name map
    pub local_map: &'a HashMap<Symbol, u16>,
    /// Parent's upvalues (for transitive capturing)
    #[allow(dead_code)]
    pub upvalues: &'a [Upvalue],
    /// Parent's upvalue name map (for transitive capturing)
    pub upvalue_names: &'a HashMap<Symbol, u16>,
    /// Parent's boxed locals (for mutable captures)
    pub boxed_locals: &'a HashSet<Symbol>,
}
