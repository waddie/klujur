// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode compiler: transforms Klujur AST to bytecode.
//!
//! The compiler operates in two phases:
//! 1. Analysis: resolve variables, determine captures, identify mutables
//! 2. Code generation: emit bytecode instructions

pub mod analysis;
pub mod codegen;

pub use analysis::{Analyser, AnalysisResult, VarKind, VariableInfo};
pub use codegen::Compiler;
