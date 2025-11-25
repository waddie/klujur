// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode compiler: transforms Klujur AST to bytecode.
//!
//! The compiler operates in two phases:
//! 1. Analysis: resolve variables, determine captures, identify mutables
//! 2. Code generation: emit bytecode instructions

pub mod analysis;
pub mod codegen;
pub mod emit;
pub mod types;
pub mod visitor;

pub use analysis::{Analyser, AnalysisResult, VarKind, VariableInfo};
pub use codegen::Compiler;
pub use types::{CompileError, EnclosingScope, Local, LoopContext, Result, Upvalue};
pub use visitor::{BoxedLocalCollector, ExprVisitor, FreeVarCollector, SetTargetCollector};
