// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Call frames for the VM.

use klujur_parser::value::KlujurVal;

/// A call frame on the VM's call stack.
#[derive(Debug, Clone)]
pub struct CallFrame {
    /// Instruction pointer (index into chunk.code).
    pub ip: usize,

    /// Stack base: index of first local variable slot.
    pub base: usize,

    /// Stack cleanup point: where to truncate on return (includes function slot).
    pub cleanup_base: usize,

    /// Index of the chunk being executed (for multi-chunk support).
    pub chunk_index: usize,

    /// Captures for the current closure (empty for non-closures).
    pub captures: Vec<KlujurVal>,
}

impl CallFrame {
    /// Create a new call frame.
    pub fn new(base: usize, chunk_index: usize) -> Self {
        Self {
            ip: 0,
            base,
            cleanup_base: base,
            chunk_index,
            captures: Vec::new(),
        }
    }

    /// Create a new call frame with separate cleanup base.
    pub fn new_with_cleanup(
        base: usize,
        cleanup_base: usize,
        chunk_index: usize,
        captures: Vec<KlujurVal>,
    ) -> Self {
        Self {
            ip: 0,
            base,
            cleanup_base,
            chunk_index,
            captures,
        }
    }
}
