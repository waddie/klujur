// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Heap cell opcode handlers: Alloc, LoadHeap, StoreHeap, LoadLocalHeap, StoreLocalHeap.

use klujur_parser::value::KlujurVal;

use crate::chunk::{HeapCell, HeapCellWrapper};
use crate::opcode::OpCode;
use crate::utils::get_heap_cell;
use crate::vm::{Result, RuntimeError, VM};

impl VM {
    /// Execute a heap cell opcode.
    pub(crate) fn execute_heap(&mut self, op: OpCode) -> Result<()> {
        match op {
            OpCode::Alloc => {
                // Allocate a new heap cell containing top of stack
                let val = self.stack.pop()?;
                let cell = HeapCell::new(val);
                self.stack.push(KlujurVal::custom(HeapCellWrapper(cell)));
            }
            OpCode::LoadHeap(idx) => {
                // Load value from heap cell in captures[idx]
                let captures = &self.frame().captures;
                if (idx as usize) < captures.len() {
                    let cell_val = &captures[idx as usize];
                    let cell = get_heap_cell(cell_val, &format!("LoadHeap: captures[{}]", idx))?;
                    let val = cell.get();
                    self.stack.push(val);
                } else {
                    return Err(RuntimeError::Internal(format!(
                        "LoadHeap: capture index {} out of bounds (have {})",
                        idx,
                        captures.len()
                    )));
                }
            }
            OpCode::StoreHeap(idx) => {
                // Store value to heap cell in captures[idx]
                let val = self.stack.pop()?;
                let captures = &self.frame().captures;
                if (idx as usize) < captures.len() {
                    let cell_val = &captures[idx as usize];
                    let cell = get_heap_cell(cell_val, &format!("StoreHeap: captures[{}]", idx))?;
                    cell.set(val);
                } else {
                    return Err(RuntimeError::Internal(format!(
                        "StoreHeap: capture index {} out of bounds (have {})",
                        idx,
                        captures.len()
                    )));
                }
            }
            OpCode::LoadLocalHeap(slot) => {
                // Load value from heap cell in local slot
                let base = self.frame().base;
                let cell_val = self.stack.get(base + slot as usize)?;
                let cell = get_heap_cell(&cell_val, &format!("LoadLocalHeap: local {}", slot))?;
                let val = cell.get();
                self.stack.push(val);
            }
            OpCode::StoreLocalHeap(slot) => {
                // Store value to heap cell in local slot
                let val = self.stack.pop()?;
                let base = self.frame().base;
                let cell_val = self.stack.get(base + slot as usize)?;
                let cell = get_heap_cell(&cell_val, &format!("StoreLocalHeap: local {}", slot))?;
                cell.set(val);
            }
            _ => {
                return Err(RuntimeError::Internal(format!(
                    "execute_heap: unexpected opcode {:?}",
                    op
                )));
            }
        }
        Ok(())
    }
}
