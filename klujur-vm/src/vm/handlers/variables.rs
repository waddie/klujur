// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Variable opcode handlers: LoadLocal, StoreLocal, LoadGlobal, DefGlobal, LoadCapture.

use klujur_parser::value::KlujurVal;

use crate::opcode::OpCode;
use crate::vm::{Result, RuntimeError, VM, resolve_global};

impl VM {
    /// Execute a variable opcode.
    pub(crate) fn execute_variables(&mut self, op: OpCode) -> Result<()> {
        match op {
            OpCode::LoadLocal(slot) => {
                let base = self.frame().base;
                let val = self.stack.get(base + slot as usize)?;
                self.stack.push(val);
            }
            OpCode::StoreLocal(slot) => {
                let val = self.stack.pop()?;
                let base = self.frame().base;
                self.stack.set(base + slot as usize, val)?;
            }
            OpCode::LoadGlobal(idx) => {
                let name = self.get_constant(idx)?;
                let name_str = match &name {
                    // Use Display to get full qualified name (ns/name or name)
                    KlujurVal::Symbol(s, _) => s.to_string(),
                    _ => {
                        return Err(RuntimeError::Internal("Global name must be symbol".into()));
                    }
                };
                // First check VM's own globals, then fall back to thread-local resolver
                let val = self
                    .globals
                    .get(&name_str)
                    .cloned()
                    .or_else(|| resolve_global(&name_str))
                    .ok_or(RuntimeError::UndefinedVariable(name_str))?;
                self.stack.push(val);
            }
            OpCode::DefGlobal(idx) => {
                let name = self.get_constant(idx)?;
                let name_str = match &name {
                    KlujurVal::Symbol(s, _) => s.name().to_string(),
                    _ => {
                        return Err(RuntimeError::Internal("Global name must be symbol".into()));
                    }
                };
                let val = self.stack.pop()?;
                self.globals.insert(name_str, val.clone());
                self.stack.push(val); // def returns the value
            }
            OpCode::LoadCapture(idx) => {
                let captures = &self.frame().captures;
                if (idx as usize) < captures.len() {
                    let val = captures[idx as usize].clone();
                    self.stack.push(val);
                } else {
                    return Err(RuntimeError::Internal(format!(
                        "Capture index {} out of bounds (have {})",
                        idx,
                        captures.len()
                    )));
                }
            }
            _ => {
                return Err(RuntimeError::Internal(format!(
                    "execute_variables: unexpected opcode {:?}",
                    op
                )));
            }
        }
        Ok(())
    }
}
