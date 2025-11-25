// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Control flow opcode handlers: Jump, Call, Return, TailCall, Closure, arity checks.

use std::rc::Rc;

use klujur_parser::value::KlujurVal;

use crate::chunk::{BytecodeFn, BytecodeFnWrapper, HeapCell, HeapCellWrapper};
use crate::compiler::codegen::FunctionPrototypeWrapper;
use crate::opcode::OpCode;
use crate::utils::{check_arity, is_falsy};
use crate::vm::frame::CallFrame;
use crate::vm::{Result, RuntimeError, VM, call_external_fn};

impl VM {
    /// Execute a control flow opcode.
    pub(crate) fn execute_control(&mut self, op: OpCode) -> Result<ControlFlow> {
        match op {
            // Jump instructions
            OpCode::Jump(offset) => {
                self.jump(offset)?;
            }
            OpCode::JumpIfFalse(offset) => {
                let val = self.stack.peek(0)?;
                if is_falsy(&val) {
                    self.jump(offset)?;
                }
            }
            OpCode::JumpIfTrue(offset) => {
                let val = self.stack.peek(0)?;
                if !is_falsy(&val) {
                    self.jump(offset)?;
                }
            }
            OpCode::PopJumpIfFalse(offset) => {
                let val = self.stack.pop()?;
                if is_falsy(&val) {
                    self.jump(offset)?;
                }
            }
            OpCode::PopJumpIfTrue(offset) => {
                let val = self.stack.pop()?;
                if !is_falsy(&val) {
                    self.jump(offset)?;
                }
            }

            // Function calls
            OpCode::Call(argc) => {
                self.call(argc as usize)?;
            }
            OpCode::TailCall(argc) => {
                self.tail_call(argc as usize)?;
            }
            OpCode::Return => {
                let result = self.stack.pop()?;

                // Pop frame
                let frame = self.frames.pop().unwrap();

                // If no more frames, we're done
                if self.frames.is_empty() {
                    return Ok(ControlFlow::Return(result));
                }

                // Restore stack to cleanup point (removes function and args) and push result
                self.stack.truncate(frame.cleanup_base);
                self.stack.push(result);
            }

            // Arity checking for multi-arity functions
            OpCode::CheckArity(expected) => {
                let argc = self.frame().argc;
                if argc != expected {
                    return Err(RuntimeError::ArityError {
                        expected: expected as usize,
                        got: argc as usize,
                    });
                }
            }
            OpCode::CheckArityAtLeast(min) => {
                let argc = self.frame().argc;
                if argc < min {
                    return Err(RuntimeError::ArityError {
                        expected: min as usize,
                        got: argc as usize,
                    });
                }
            }
            OpCode::ArityDispatch(entry_count) => {
                let argc = self.frame().argc;

                // Read all dispatch table entries into a vec first
                // (since jump will modify IP, we can't mix reading and jumping)
                let mut entries = Vec::with_capacity(entry_count as usize);
                for _ in 0..entry_count {
                    let entry_op = self.read_op()?;
                    if let OpCode::ArityEntry {
                        arity,
                        has_rest,
                        offset,
                    } = entry_op
                    {
                        entries.push((arity, has_rest, offset));
                    } else {
                        return Err(RuntimeError::Internal(format!(
                            "Expected ArityEntry in dispatch table, got {:?}",
                            entry_op
                        )));
                    }
                }

                // Find a matching arity and jump
                let mut found = false;
                for (arity, has_rest, offset) in entries {
                    let matches = if has_rest {
                        argc >= arity
                    } else {
                        argc == arity
                    };
                    if matches {
                        self.jump(offset)?;
                        found = true;
                        break;
                    }
                }

                if !found {
                    return Err(RuntimeError::ArityError {
                        expected: 0, // Could improve error message
                        got: argc as usize,
                    });
                }
            }
            OpCode::ArityEntry { .. } => {
                // ArityEntry should only be read within ArityDispatch
                return Err(RuntimeError::Internal(
                    "ArityEntry outside ArityDispatch context".into(),
                ));
            }

            // Closures
            OpCode::Closure(idx) => {
                self.execute_closure(idx)?;
            }
            // These are handled by the Closure instruction above
            OpCode::CaptureLocal(_)
            | OpCode::CaptureUpvalue(_)
            | OpCode::CaptureHeapLocal(_)
            | OpCode::CaptureHeapUpvalue(_) => {
                return Err(RuntimeError::Internal(
                    "Capture instruction outside Closure context".into(),
                ));
            }

            _ => {
                return Err(RuntimeError::Internal(format!(
                    "execute_control: unexpected opcode {:?}",
                    op
                )));
            }
        }
        Ok(ControlFlow::Continue)
    }

    fn execute_closure(&mut self, idx: u16) -> Result<()> {
        let proto_val = self.get_constant(idx)?;
        // Extract FunctionPrototype from the Custom wrapper
        if let KlujurVal::Custom(custom) = proto_val {
            if let Some(wrapper) = custom.downcast_ref::<FunctionPrototypeWrapper>() {
                let proto = Rc::new(wrapper.0.clone());
                let upvalue_count = proto.upvalue_count as usize;

                // Read capture instructions and build captures vector
                let mut captures = Vec::with_capacity(upvalue_count);
                for _ in 0..upvalue_count {
                    let capture_op = self.read_op()?;
                    match capture_op {
                        OpCode::CaptureLocal(slot) => {
                            // Capture from current frame's locals
                            let base = self.frame().base;
                            let val = self.stack.get(base + slot as usize)?;
                            captures.push(val);
                        }
                        OpCode::CaptureUpvalue(idx) => {
                            // Capture from current closure's captures (transitive capture)
                            let current_captures = &self.frame().captures;
                            if (idx as usize) < current_captures.len() {
                                let val = current_captures[idx as usize].clone();
                                captures.push(val);
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "Upvalue index {} out of bounds (have {})",
                                    idx,
                                    current_captures.len()
                                )));
                            }
                        }
                        OpCode::CaptureHeapLocal(slot) => {
                            // Capture a mutable local as a heap cell
                            let base = self.frame().base;
                            let val = self.stack.get(base + slot as usize)?;
                            // Check if it's already a heap cell (from a previous capture)
                            if let KlujurVal::Custom(custom) = &val {
                                if custom.downcast_ref::<HeapCellWrapper>().is_some() {
                                    // Already a heap cell, just capture it
                                    captures.push(val);
                                } else {
                                    // Wrap in a new heap cell
                                    let cell = HeapCell::new(val);
                                    let cell_val = KlujurVal::custom(HeapCellWrapper(cell.clone()));
                                    // Store the cell back to the local slot so other closures share it
                                    self.stack.set(base + slot as usize, cell_val.clone())?;
                                    captures.push(cell_val);
                                }
                            } else {
                                // Wrap in a new heap cell
                                let cell = HeapCell::new(val);
                                let cell_val = KlujurVal::custom(HeapCellWrapper(cell.clone()));
                                // Store the cell back to the local slot so other closures share it
                                self.stack.set(base + slot as usize, cell_val.clone())?;
                                captures.push(cell_val);
                            }
                        }
                        OpCode::CaptureHeapUpvalue(idx) => {
                            // Capture heap cell from parent's captures (transitive)
                            let current_captures = &self.frame().captures;
                            if (idx as usize) < current_captures.len() {
                                let cell_val = current_captures[idx as usize].clone();
                                // Should already be a HeapCell from parent
                                captures.push(cell_val);
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "Heap upvalue index {} out of bounds (have {})",
                                    idx,
                                    current_captures.len()
                                )));
                            }
                        }
                        _ => {
                            return Err(RuntimeError::Internal(format!(
                                "Expected capture instruction, got {:?}",
                                capture_op
                            )));
                        }
                    }
                }

                let bytecode_fn = BytecodeFn::with_captures(proto, captures);
                let fn_wrapper = BytecodeFnWrapper(Rc::new(bytecode_fn));
                self.stack.push(KlujurVal::custom(fn_wrapper));
            } else {
                return Err(RuntimeError::Internal(
                    "Closure constant is not a FunctionPrototype".into(),
                ));
            }
        } else {
            return Err(RuntimeError::Internal(
                "Closure constant is not a Custom value".into(),
            ));
        }
        Ok(())
    }

    pub(crate) fn call(&mut self, argc: usize) -> Result<()> {
        // Stack layout: [... fn arg0 arg1 ... argN]
        // The function is at stack[top - argc - 1]
        let fn_index = self.stack.len() - argc - 1;
        let callee = self.stack.get(fn_index)?;

        // Check if it's a bytecode function
        if let KlujurVal::Custom(custom) = &callee
            && let Some(wrapper) = custom.downcast_ref::<BytecodeFnWrapper>()
        {
            let bytecode_fn: Rc<BytecodeFn> = Rc::clone(&wrapper.0);
            let arity = bytecode_fn.arity() as usize;
            let has_rest = bytecode_fn.has_rest();
            let is_multi_arity = bytecode_fn.is_multi_arity();

            // Multi-arity functions handle their own arity dispatch via ArityDispatch opcode
            // Skip arity checking and rest handling for them
            check_arity(argc, arity, has_rest, is_multi_arity)?;

            // Add the function's chunk to our chunks list (Rc::clone is cheap)
            let chunk = bytecode_fn.chunk();
            self.chunks.push(chunk);
            let chunk_index = self.chunks.len() - 1;

            // Calculate the frame base
            // For named functions: slot 0 = function (for self-recursion)
            // For anonymous functions: slot 0 = first argument
            let has_name = bytecode_fn.name().is_some();
            let frame_base = if has_name { fn_index } else { fn_index + 1 };

            // Handle rest parameter if present (only for non-multi-arity functions)
            if !is_multi_arity {
                if has_rest && argc > arity {
                    // Collect extra args into a list
                    let extra_start = fn_index + 1 + arity;
                    let extra_count = argc - arity;
                    let mut rest_items = Vec::new();
                    for i in 0..extra_count {
                        rest_items.push(self.stack.get(extra_start + i)?);
                    }
                    let rest_list = KlujurVal::list(rest_items);

                    // Remove extra args and push the rest list
                    // First truncate to remove extra args
                    self.stack.truncate(extra_start);
                    self.stack.push(rest_list);
                } else if has_rest {
                    // No extra args, push empty list for rest parameter
                    self.stack.push(KlujurVal::list(vec![]));
                }
            }

            // Push new frame with captures from the closure
            // cleanup_base = fn_index ensures the function slot is cleaned up on return
            let captures = bytecode_fn.captures.clone();
            self.frames.push(CallFrame::new_with_argc(
                frame_base,
                fn_index,
                chunk_index,
                captures,
                argc as u8,
            ));

            return Ok(());
        }

        // Not a bytecode function - try external function caller (for native functions, etc.)
        self.call_external(fn_index, argc, &callee)
    }

    pub(crate) fn tail_call(&mut self, argc: usize) -> Result<()> {
        // For tail calls, we reuse the current frame instead of pushing a new one
        // Stack layout: [... fn arg0 arg1 ... argN]
        let fn_index = self.stack.len() - argc - 1;
        let callee = self.stack.get(fn_index)?;

        if let KlujurVal::Custom(custom) = &callee
            && let Some(wrapper) = custom.downcast_ref::<BytecodeFnWrapper>()
        {
            let bytecode_fn: Rc<BytecodeFn> = Rc::clone(&wrapper.0);
            let arity = bytecode_fn.arity() as usize;
            let has_rest = bytecode_fn.has_rest();
            let has_name = bytecode_fn.name().is_some();
            let is_multi_arity = bytecode_fn.is_multi_arity();

            // Multi-arity functions handle their own arity dispatch via ArityDispatch opcode
            check_arity(argc, arity, has_rest, is_multi_arity)?;

            // Get current frame's cleanup_base - this stays the same
            let cleanup_base = self.frame().cleanup_base;

            // New base: named functions have fn at slot 0, anonymous skip it
            let new_base = if has_name {
                cleanup_base
            } else {
                cleanup_base + 1
            };

            // Handle rest parameter (only for non-multi-arity functions)
            let rest_list = if !is_multi_arity {
                if has_rest && argc > arity {
                    let extra_start = fn_index + 1 + arity;
                    let extra_count = argc - arity;
                    let mut rest_items = Vec::new();
                    for i in 0..extra_count {
                        rest_items.push(self.stack.get(extra_start + i)?);
                    }
                    Some(KlujurVal::list(rest_items))
                } else if has_rest {
                    Some(KlujurVal::list(vec![]))
                } else {
                    None
                }
            } else {
                None
            };

            // Copy function value to cleanup_base (for named functions, this is slot 0)
            let fn_val = self.stack.get(fn_index)?;
            self.stack.set(cleanup_base, fn_val)?;

            // Copy regular args (for multi-arity, copy all argc args)
            let args_to_copy = if is_multi_arity { argc } else { arity };
            for i in 0..args_to_copy {
                let arg = self.stack.get(fn_index + 1 + i)?;
                self.stack.set(new_base + i, arg)?;
            }

            // Add rest list if needed
            let truncate_to = if let Some(rest) = rest_list {
                self.stack.set(new_base + arity, rest)?;
                new_base + arity + 1
            } else {
                new_base + argc
            };

            self.stack.truncate(truncate_to);

            // Update chunk and reset IP (Rc::clone is cheap)
            let chunk = bytecode_fn.chunk();
            self.chunks.push(chunk);
            let chunk_index = self.chunks.len() - 1;

            // Update frame with new function's captures
            let captures = bytecode_fn.captures.clone();
            let frame = self.frame_mut();
            frame.base = new_base;
            frame.chunk_index = chunk_index;
            frame.ip = 0;
            frame.captures = captures;
            frame.argc = argc as u8;
            // cleanup_base stays the same

            return Ok(());
        }

        // Not a bytecode function - handle as external call (no TCO benefit for external)
        self.call_external(fn_index, argc, &callee)
    }

    /// Call an external (non-bytecode) function.
    fn call_external(&mut self, fn_index: usize, argc: usize, callee: &KlujurVal) -> Result<()> {
        // Collect arguments from the stack
        let args: Vec<KlujurVal> = (0..argc)
            .map(|i| self.stack.get(fn_index + 1 + i))
            .collect::<Result<Vec<_>>>()?;

        // Call the external function
        let result = call_external_fn(callee, &args).map_err(RuntimeError::Internal)?;

        // Pop the function and arguments, then push the result
        self.stack.truncate(fn_index);
        self.stack.push(result);
        Ok(())
    }
}

/// Control flow result from executing an opcode.
pub enum ControlFlow {
    /// Continue execution.
    Continue,
    /// Return from the VM with the given value.
    Return(KlujurVal),
}
