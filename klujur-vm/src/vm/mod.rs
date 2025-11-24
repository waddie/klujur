// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Stack-based virtual machine for executing Klujur bytecode.

pub mod frame;
pub mod stack;

use std::rc::Rc;

use klujur_parser::value::KlujurVal;

use crate::chunk::{BytecodeFn, BytecodeFnWrapper, Chunk};
use crate::compiler::codegen::FunctionPrototypeWrapper;
use crate::opcode::OpCode;

pub use frame::CallFrame;
pub use stack::ValueStack;

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

/// The Klujur virtual machine.
pub struct VM {
    /// Value stack.
    stack: ValueStack,

    /// Call frame stack.
    frames: Vec<CallFrame>,

    /// Chunks being executed (index 0 is the main chunk).
    chunks: Vec<Chunk>,

    /// Global variables (for standalone execution).
    globals: std::collections::HashMap<String, KlujurVal>,
}

impl VM {
    /// Create a new VM.
    pub fn new() -> Self {
        Self {
            stack: ValueStack::new(),
            frames: Vec::new(),
            chunks: Vec::new(),
            globals: std::collections::HashMap::new(),
        }
    }

    /// Execute a chunk of bytecode.
    pub fn run(&mut self, chunk: Chunk) -> Result<KlujurVal> {
        // Store the chunk
        self.chunks.push(chunk);
        let chunk_index = self.chunks.len() - 1;

        // Create initial frame
        self.frames.push(CallFrame::new(0, chunk_index));

        // Run the main loop
        self.run_loop()
    }

    fn run_loop(&mut self) -> Result<KlujurVal> {
        loop {
            let op = self.read_op()?;

            match op {
                // Constants & Stack
                OpCode::Const(idx) => {
                    let val = self.get_constant(idx)?;
                    self.stack.push(val);
                }
                OpCode::Pop => {
                    self.stack.pop()?;
                }
                OpCode::Dup => {
                    let val = self.stack.peek(0)?;
                    self.stack.push(val);
                }

                // Variables
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
                        KlujurVal::Symbol(s, _) => s.name().to_string(),
                        _ => {
                            return Err(RuntimeError::Internal(
                                "Global name must be symbol".into(),
                            ));
                        }
                    };
                    let val = self
                        .globals
                        .get(&name_str)
                        .cloned()
                        .ok_or(RuntimeError::UndefinedVariable(name_str))?;
                    self.stack.push(val);
                }
                OpCode::DefGlobal(idx) => {
                    let name = self.get_constant(idx)?;
                    let name_str = match &name {
                        KlujurVal::Symbol(s, _) => s.name().to_string(),
                        _ => {
                            return Err(RuntimeError::Internal(
                                "Global name must be symbol".into(),
                            ));
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

                // Heap cells
                OpCode::Alloc | OpCode::LoadHeap(_) | OpCode::StoreHeap(_) => {
                    // TODO: Implement heap cells
                    return Err(RuntimeError::Internal(
                        "Heap cells not yet implemented".into(),
                    ));
                }

                // Control Flow
                OpCode::Jump(offset) => {
                    self.jump(offset);
                }
                OpCode::JumpIfFalse(offset) => {
                    let val = self.stack.peek(0)?;
                    if is_falsy(&val) {
                        self.jump(offset);
                    }
                }
                OpCode::JumpIfTrue(offset) => {
                    let val = self.stack.peek(0)?;
                    if !is_falsy(&val) {
                        self.jump(offset);
                    }
                }
                OpCode::PopJumpIfFalse(offset) => {
                    let val = self.stack.pop()?;
                    if is_falsy(&val) {
                        self.jump(offset);
                    }
                }
                OpCode::PopJumpIfTrue(offset) => {
                    let val = self.stack.pop()?;
                    if !is_falsy(&val) {
                        self.jump(offset);
                    }
                }

                // Function Calls
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
                        return Ok(result);
                    }

                    // Restore stack to cleanup point (removes function and args) and push result
                    self.stack.truncate(frame.cleanup_base);
                    self.stack.push(result);
                }

                // Closures
                OpCode::Closure(idx) => {
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
                                        // Capture from current closure's captures
                                        // This requires access to the current function's captures
                                        // For now, we don't support transitive captures
                                        return Err(RuntimeError::Internal(format!(
                                            "CaptureUpvalue({}) not yet supported",
                                            idx
                                        )));
                                    }
                                    OpCode::CaptureHeapLocal(_) | OpCode::CaptureHeapUpvalue(_) => {
                                        return Err(RuntimeError::Internal(
                                            "Heap captures not yet implemented".into(),
                                        ));
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

                // Arithmetic
                OpCode::Add => self.binary_num_op(|a, b| a + b, |a, b| a + b, "+")?,
                OpCode::Sub => self.binary_num_op(|a, b| a - b, |a, b| a - b, "-")?,
                OpCode::Mul => self.binary_num_op(|a, b| a * b, |a, b| a * b, "*")?,
                OpCode::Div => {
                    let b = self.stack.pop()?;
                    let a = self.stack.pop()?;
                    match (&a, &b) {
                        (KlujurVal::Int(x), KlujurVal::Int(y)) => {
                            if *y == 0 {
                                return Err(RuntimeError::DivisionByZero);
                            }
                            self.stack.push(KlujurVal::Int(x / y));
                        }
                        (KlujurVal::Float(x), KlujurVal::Float(y)) => {
                            self.stack.push(KlujurVal::Float(x / y));
                        }
                        (KlujurVal::Int(x), KlujurVal::Float(y)) => {
                            self.stack.push(KlujurVal::Float(*x as f64 / y));
                        }
                        (KlujurVal::Float(x), KlujurVal::Int(y)) => {
                            self.stack.push(KlujurVal::Float(x / *y as f64));
                        }
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "number".into(),
                                got: format!("{} / {}", type_name(&a), type_name(&b)),
                            });
                        }
                    }
                }

                // Comparison
                OpCode::Eq => {
                    let b = self.stack.pop()?;
                    let a = self.stack.pop()?;
                    self.stack.push(KlujurVal::Bool(a == b));
                }
                OpCode::Lt => self.comparison_op(|a, b| a < b, |a, b| a < b, "<")?,
                OpCode::Gt => self.comparison_op(|a, b| a > b, |a, b| a > b, ">")?,
                OpCode::Le => self.comparison_op(|a, b| a <= b, |a, b| a <= b, "<=")?,
                OpCode::Ge => self.comparison_op(|a, b| a >= b, |a, b| a >= b, ">=")?,

                // Sequence operations
                OpCode::Cons => {
                    let rest = self.stack.pop()?;
                    let first = self.stack.pop()?;
                    let list = match rest {
                        KlujurVal::List(l, _) => {
                            let mut v = vec![first];
                            v.extend(l.iter().cloned());
                            KlujurVal::list(v)
                        }
                        KlujurVal::Nil => KlujurVal::list(vec![first]),
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "list or nil".into(),
                                got: type_name(&rest).into(),
                            });
                        }
                    };
                    self.stack.push(list);
                }
                OpCode::First => {
                    let coll = self.stack.pop()?;
                    let first = match &coll {
                        KlujurVal::List(l, _) => l.front().cloned().unwrap_or(KlujurVal::Nil),
                        KlujurVal::Vector(v, _) => v.front().cloned().unwrap_or(KlujurVal::Nil),
                        KlujurVal::Nil => KlujurVal::Nil,
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "sequence".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(first);
                }
                OpCode::Rest => {
                    let coll = self.stack.pop()?;
                    let rest = match &coll {
                        KlujurVal::List(l, _) => {
                            if l.is_empty() {
                                KlujurVal::list(vec![])
                            } else {
                                KlujurVal::list(l.iter().skip(1).cloned().collect())
                            }
                        }
                        KlujurVal::Vector(v, _) => {
                            if v.is_empty() {
                                KlujurVal::list(vec![])
                            } else {
                                KlujurVal::list(v.iter().skip(1).cloned().collect())
                            }
                        }
                        KlujurVal::Nil => KlujurVal::list(vec![]),
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "sequence".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(rest);
                }

                // Constants
                OpCode::Nil => self.stack.push(KlujurVal::Nil),
                OpCode::True => self.stack.push(KlujurVal::Bool(true)),
                OpCode::False => self.stack.push(KlujurVal::Bool(false)),
                OpCode::Not => {
                    let val = self.stack.pop()?;
                    self.stack.push(KlujurVal::Bool(is_falsy(&val)));
                }
            }
        }
    }

    fn read_op(&mut self) -> Result<OpCode> {
        let frame = self
            .frames
            .last_mut()
            .ok_or(RuntimeError::Internal("No active frame".into()))?;
        let chunk = &self.chunks[frame.chunk_index];
        let op = chunk
            .code
            .get(frame.ip)
            .copied()
            .ok_or(RuntimeError::Internal("IP out of bounds".into()))?;
        frame.ip += 1;
        Ok(op)
    }

    fn frame(&self) -> &CallFrame {
        self.frames.last().expect("No active frame")
    }

    fn frame_mut(&mut self) -> &mut CallFrame {
        self.frames.last_mut().expect("No active frame")
    }

    fn current_chunk(&self) -> &Chunk {
        &self.chunks[self.frame().chunk_index]
    }

    fn get_constant(&self, idx: u16) -> Result<KlujurVal> {
        self.current_chunk()
            .constants
            .get(idx as usize)
            .cloned()
            .ok_or(RuntimeError::Internal(
                "Constant index out of bounds".into(),
            ))
    }

    fn jump(&mut self, offset: i16) {
        let frame = self.frame_mut();
        frame.ip = (frame.ip as i32 + offset as i32) as usize;
    }

    fn call(&mut self, argc: usize) -> Result<()> {
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

            // Check arity
            if has_rest {
                if argc < arity {
                    return Err(RuntimeError::ArityError {
                        expected: arity,
                        got: argc,
                    });
                }
            } else if argc != arity {
                return Err(RuntimeError::ArityError {
                    expected: arity,
                    got: argc,
                });
            }

            // Add the function's chunk to our chunks list
            let chunk = bytecode_fn.chunk().clone();
            self.chunks.push(chunk);
            let chunk_index = self.chunks.len() - 1;

            // Calculate the frame base
            // For named functions: slot 0 = function (for self-recursion)
            // For anonymous functions: slot 0 = first argument
            let has_name = bytecode_fn.name().is_some();
            let frame_base = if has_name { fn_index } else { fn_index + 1 };

            // Handle rest parameter if present
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

            // If the function has a name, we need to make it available at slot 0
            // The stack currently has: [fn arg0 arg1 ... argN (rest)]
            // For self-recursion, we store the function at its own slot
            if has_name {
                // The function is already at fn_index, which becomes slot 0
                // Arguments follow at slots 1, 2, etc.
            }

            // Push new frame with captures from the closure
            // cleanup_base = fn_index ensures the function slot is cleaned up on return
            let captures = bytecode_fn.captures.clone();
            self.frames.push(CallFrame::new_with_cleanup(
                frame_base,
                fn_index,
                chunk_index,
                captures,
            ));

            return Ok(());
        }

        // Not a bytecode function - could be a native function in the future
        Err(RuntimeError::NotCallable(type_name(&callee).into()))
    }

    fn tail_call(&mut self, argc: usize) -> Result<()> {
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

            // Check arity
            if has_rest {
                if argc < arity {
                    return Err(RuntimeError::ArityError {
                        expected: arity,
                        got: argc,
                    });
                }
            } else if argc != arity {
                return Err(RuntimeError::ArityError {
                    expected: arity,
                    got: argc,
                });
            }

            // Get current frame's cleanup_base - this stays the same
            let cleanup_base = self.frame().cleanup_base;

            // New base: named functions have fn at slot 0, anonymous skip it
            let new_base = if has_name {
                cleanup_base
            } else {
                cleanup_base + 1
            };

            // Handle rest parameter
            let rest_list = if has_rest && argc > arity {
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
            };

            // Copy function value to cleanup_base (for named functions, this is slot 0)
            let fn_val = self.stack.get(fn_index)?;
            self.stack.set(cleanup_base, fn_val)?;

            // Copy regular args
            for i in 0..arity {
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

            // Update chunk and reset IP
            let chunk = bytecode_fn.chunk().clone();
            self.chunks.push(chunk);
            let chunk_index = self.chunks.len() - 1;

            // Update frame with new function's captures
            let captures = bytecode_fn.captures.clone();
            let frame = self.frame_mut();
            frame.base = new_base;
            frame.chunk_index = chunk_index;
            frame.ip = 0;
            frame.captures = captures;
            // cleanup_base stays the same

            return Ok(());
        }

        Err(RuntimeError::NotCallable(type_name(&callee).into()))
    }

    fn binary_num_op<FI, FF>(&mut self, int_op: FI, float_op: FF, name: &str) -> Result<()>
    where
        FI: Fn(i64, i64) -> i64,
        FF: Fn(f64, f64) -> f64,
    {
        let b = self.stack.pop()?;
        let a = self.stack.pop()?;

        let result = match (&a, &b) {
            (KlujurVal::Int(x), KlujurVal::Int(y)) => KlujurVal::Int(int_op(*x, *y)),
            (KlujurVal::Float(x), KlujurVal::Float(y)) => KlujurVal::Float(float_op(*x, *y)),
            (KlujurVal::Int(x), KlujurVal::Float(y)) => KlujurVal::Float(float_op(*x as f64, *y)),
            (KlujurVal::Float(x), KlujurVal::Int(y)) => KlujurVal::Float(float_op(*x, *y as f64)),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: format!("{} {} {}", type_name(&a), name, type_name(&b)),
                });
            }
        };

        self.stack.push(result);
        Ok(())
    }

    fn comparison_op<FI, FF>(&mut self, int_op: FI, float_op: FF, name: &str) -> Result<()>
    where
        FI: Fn(i64, i64) -> bool,
        FF: Fn(f64, f64) -> bool,
    {
        let b = self.stack.pop()?;
        let a = self.stack.pop()?;

        let result = match (&a, &b) {
            (KlujurVal::Int(x), KlujurVal::Int(y)) => int_op(*x, *y),
            (KlujurVal::Float(x), KlujurVal::Float(y)) => float_op(*x, *y),
            (KlujurVal::Int(x), KlujurVal::Float(y)) => float_op(*x as f64, *y),
            (KlujurVal::Float(x), KlujurVal::Int(y)) => float_op(*x, *y as f64),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: format!("{} {} {}", type_name(&a), name, type_name(&b)),
                });
            }
        };

        self.stack.push(KlujurVal::Bool(result));
        Ok(())
    }
}

impl Default for VM {
    fn default() -> Self {
        Self::new()
    }
}

// Helper functions
fn is_falsy(val: &KlujurVal) -> bool {
    matches!(val, KlujurVal::Nil | KlujurVal::Bool(false))
}

fn type_name(val: &KlujurVal) -> &'static str {
    match val {
        KlujurVal::Nil => "nil",
        KlujurVal::Bool(_) => "boolean",
        KlujurVal::Int(_) => "integer",
        KlujurVal::BigInt(_) => "bigint",
        KlujurVal::Float(_) => "float",
        KlujurVal::Ratio(..) => "ratio",
        KlujurVal::BigRatio(..) => "bigratio",
        KlujurVal::Char(_) => "char",
        KlujurVal::String(_) => "string",
        KlujurVal::Symbol(..) => "symbol",
        KlujurVal::Keyword(_) => "keyword",
        KlujurVal::List(..) => "list",
        KlujurVal::Vector(..) => "vector",
        KlujurVal::Map(..) => "map",
        KlujurVal::Set(..) => "set",
        KlujurVal::Fn(_) => "function",
        KlujurVal::NativeFn(_) => "native-function",
        KlujurVal::Macro(_) => "macro",
        KlujurVal::Var(_) => "var",
        KlujurVal::Atom(_) => "atom",
        KlujurVal::Delay(_) => "delay",
        KlujurVal::LazySeq(_) => "lazy-seq",
        KlujurVal::Volatile(_) => "volatile",
        KlujurVal::Multimethod(_) => "multimethod",
        KlujurVal::Protocol(_) => "protocol",
        KlujurVal::Hierarchy(_) => "hierarchy",
        KlujurVal::Record(_) => "record",
        KlujurVal::Reduced(_) => "reduced",
        KlujurVal::SortedMapBy(_) => "sorted-map-by",
        KlujurVal::SortedSetBy(_) => "sorted-set-by",
        KlujurVal::Custom(_) => "custom",
    }
}
