// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode compiler and stack-based virtual machine for Klujur.
//!
//! This crate provides an alternative execution model to the AST-walking interpreter
//! in `klujur-core`. Code is first compiled to bytecode, then executed by a stack-based VM.

pub mod chunk;
pub mod compiler;
pub mod opcode;
pub mod vm;

pub use chunk::{BytecodeFn, BytecodeFnWrapper, Chunk, FunctionPrototype, LineInfo};
pub use opcode::OpCode;
pub use vm::{FnCaller, GlobalResolver, VM, set_fn_caller, set_global_resolver};
