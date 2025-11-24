// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Value stack for the VM.

use klujur_parser::value::KlujurVal;

use super::{Result, RuntimeError};

/// The VM's value stack.
#[derive(Debug, Default)]
pub struct ValueStack {
    values: Vec<KlujurVal>,
}

impl ValueStack {
    /// Create a new empty stack.
    pub fn new() -> Self {
        Self {
            values: Vec::with_capacity(256),
        }
    }

    /// Push a value onto the stack.
    #[inline]
    pub fn push(&mut self, value: KlujurVal) {
        self.values.push(value);
    }

    /// Pop a value from the stack.
    #[inline]
    pub fn pop(&mut self) -> Result<KlujurVal> {
        self.values.pop().ok_or(RuntimeError::StackUnderflow)
    }

    /// Peek at a value on the stack without removing it.
    /// `distance` is the offset from the top (0 = top).
    #[inline]
    pub fn peek(&self, distance: usize) -> Result<KlujurVal> {
        if distance >= self.values.len() {
            return Err(RuntimeError::StackUnderflow);
        }
        Ok(self.values[self.values.len() - 1 - distance].clone())
    }

    /// Get a value at an absolute index.
    #[inline]
    pub fn get(&self, index: usize) -> Result<KlujurVal> {
        self.values
            .get(index)
            .cloned()
            .ok_or(RuntimeError::StackUnderflow)
    }

    /// Set a value at an absolute index.
    #[inline]
    pub fn set(&mut self, index: usize, value: KlujurVal) -> Result<()> {
        if index >= self.values.len() {
            return Err(RuntimeError::StackUnderflow);
        }
        self.values[index] = value;
        Ok(())
    }

    /// Get the current stack size.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if the stack is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Truncate the stack to the given size.
    #[inline]
    pub fn truncate(&mut self, size: usize) {
        self.values.truncate(size);
    }

    /// Pop n values and return them as a vector.
    pub fn pop_n(&mut self, n: usize) -> Result<Vec<KlujurVal>> {
        if n > self.values.len() {
            return Err(RuntimeError::StackUnderflow);
        }
        let start = self.values.len() - n;
        Ok(self.values.drain(start..).collect())
    }
}
