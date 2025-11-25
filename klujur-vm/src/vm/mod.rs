// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Stack-based virtual machine for executing Klujur bytecode.

pub mod frame;
pub mod stack;

use std::cell::RefCell;
use std::rc::Rc;

use klujur_parser::value::KlujurVal;

use crate::chunk::{BytecodeFn, BytecodeFnWrapper, Chunk, HeapCell, HeapCellWrapper};
use crate::compiler::codegen::FunctionPrototypeWrapper;
use crate::opcode::OpCode;

pub use frame::CallFrame;
pub use stack::ValueStack;

/// Type for resolving global variables from an external source (e.g., the interpreter).
pub type GlobalResolver = dyn Fn(&str) -> Option<KlujurVal>;

/// Type for calling functions that the VM can't handle (e.g., native functions, interpreted fns).
/// Takes the function value and arguments, returns Ok(result) or Err(error message).
pub type FnCaller = dyn Fn(&KlujurVal, &[KlujurVal]) -> std::result::Result<KlujurVal, String>;

thread_local! {
    /// Thread-local global resolver for hybrid mode.
    /// When set, the VM will use this to resolve globals not found in its own map.
    static GLOBAL_RESOLVER: RefCell<Option<Rc<GlobalResolver>>> = const { RefCell::new(None) };
    /// Thread-local function caller for hybrid mode.
    /// When set, the VM will use this to call non-bytecode functions.
    static FN_CALLER: RefCell<Option<Rc<FnCaller>>> = const { RefCell::new(None) };
}

/// Set the global resolver for the current thread. Returns the previous resolver.
pub fn set_global_resolver(resolver: Option<Rc<GlobalResolver>>) -> Option<Rc<GlobalResolver>> {
    GLOBAL_RESOLVER.with(|r| r.replace(resolver))
}

/// Resolve a global variable using the thread-local resolver.
fn resolve_global(name: &str) -> Option<KlujurVal> {
    GLOBAL_RESOLVER.with(|r| {
        if let Some(resolver) = r.borrow().as_ref() {
            resolver(name)
        } else {
            None
        }
    })
}

/// Set the function caller for the current thread. Returns the previous caller.
pub fn set_fn_caller(caller: Option<Rc<FnCaller>>) -> Option<Rc<FnCaller>> {
    FN_CALLER.with(|c| c.replace(caller))
}

/// Call a non-bytecode function using the thread-local function caller.
fn call_external_fn(
    func: &KlujurVal,
    args: &[KlujurVal],
) -> std::result::Result<KlujurVal, String> {
    FN_CALLER.with(|c| {
        if let Some(caller) = c.borrow().as_ref() {
            caller(func, args)
        } else {
            Err("No function caller set for hybrid mode".into())
        }
    })
}

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

    /// Call a bytecode function with arguments.
    ///
    /// This is the main entry point for calling bytecode functions from the interpreter.
    pub fn call_fn(&mut self, bytecode_fn: &BytecodeFn, args: &[KlujurVal]) -> Result<KlujurVal> {
        // Check arity (skip for multi-arity functions)
        let arity = bytecode_fn.arity() as usize;
        let has_rest = bytecode_fn.has_rest();
        let is_multi_arity = bytecode_fn.is_multi_arity();

        if !is_multi_arity {
            if has_rest {
                if args.len() < arity {
                    return Err(RuntimeError::ArityError {
                        expected: arity,
                        got: args.len(),
                    });
                }
            } else if args.len() != arity {
                return Err(RuntimeError::ArityError {
                    expected: arity,
                    got: args.len(),
                });
            }
        }

        // Push the function onto the stack (for cleanup purposes)
        let fn_val = KlujurVal::custom(BytecodeFnWrapper(Rc::new(bytecode_fn.clone())));
        let fn_index = self.stack.len();
        self.stack.push(fn_val);

        // Push the arguments
        for arg in args {
            self.stack.push(arg.clone());
        }

        // Handle rest parameter if present (only for non-multi-arity functions)
        if !is_multi_arity {
            if has_rest && args.len() > arity {
                let extra_start = fn_index + 1 + arity;
                let extra_count = args.len() - arity;
                let mut rest_items = Vec::new();
                for i in 0..extra_count {
                    rest_items.push(self.stack.get(extra_start + i)?);
                }
                let rest_list = KlujurVal::list(rest_items);
                self.stack.truncate(extra_start);
                self.stack.push(rest_list);
            } else if has_rest {
                self.stack.push(KlujurVal::list(vec![]));
            }
        }

        // Add the function's chunk to our chunks list
        let chunk = bytecode_fn.chunk().clone();
        self.chunks.push(chunk);
        let chunk_index = self.chunks.len() - 1;

        // Calculate frame base
        let has_name = bytecode_fn.name().is_some();
        let frame_base = if has_name { fn_index } else { fn_index + 1 };

        // Push the frame with argc for multi-arity dispatch
        let captures = bytecode_fn.captures.clone();
        self.frames.push(CallFrame::new_with_argc(
            frame_base,
            fn_index,
            chunk_index,
            captures,
            args.len() as u8,
        ));

        // Run the function
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
                        // Use Display to get full qualified name (ns/name or name)
                        KlujurVal::Symbol(s, _) => s.to_string(),
                        _ => {
                            return Err(RuntimeError::Internal(
                                "Global name must be symbol".into(),
                            ));
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

                // Heap cells for mutable captures
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
                        if let KlujurVal::Custom(custom) = cell_val {
                            if let Some(wrapper) = custom.downcast_ref::<HeapCellWrapper>() {
                                let val = wrapper.0.get();
                                self.stack.push(val);
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "LoadHeap: captures[{}] is not a HeapCell",
                                    idx
                                )));
                            }
                        } else {
                            return Err(RuntimeError::Internal(format!(
                                "LoadHeap: captures[{}] is not a Custom value",
                                idx
                            )));
                        }
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
                        if let KlujurVal::Custom(custom) = cell_val {
                            if let Some(wrapper) = custom.downcast_ref::<HeapCellWrapper>() {
                                wrapper.0.set(val);
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "StoreHeap: captures[{}] is not a HeapCell",
                                    idx
                                )));
                            }
                        } else {
                            return Err(RuntimeError::Internal(format!(
                                "StoreHeap: captures[{}] is not a Custom value",
                                idx
                            )));
                        }
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
                    if let KlujurVal::Custom(custom) = &cell_val {
                        if let Some(wrapper) = custom.downcast_ref::<HeapCellWrapper>() {
                            let val = wrapper.0.get();
                            self.stack.push(val);
                        } else {
                            return Err(RuntimeError::Internal(format!(
                                "LoadLocalHeap: local {} is not a HeapCell",
                                slot
                            )));
                        }
                    } else {
                        return Err(RuntimeError::Internal(format!(
                            "LoadLocalHeap: local {} is not a Custom value",
                            slot
                        )));
                    }
                }
                OpCode::StoreLocalHeap(slot) => {
                    // Store value to heap cell in local slot
                    let val = self.stack.pop()?;
                    let base = self.frame().base;
                    let cell_val = self.stack.get(base + slot as usize)?;
                    if let KlujurVal::Custom(custom) = &cell_val {
                        if let Some(wrapper) = custom.downcast_ref::<HeapCellWrapper>() {
                            wrapper.0.set(val);
                        } else {
                            return Err(RuntimeError::Internal(format!(
                                "StoreLocalHeap: local {} is not a HeapCell",
                                slot
                            )));
                        }
                    } else {
                        return Err(RuntimeError::Internal(format!(
                            "StoreLocalHeap: local {} is not a Custom value",
                            slot
                        )));
                    }
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
                            self.jump(offset);
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
                                                let cell_val = KlujurVal::custom(HeapCellWrapper(
                                                    cell.clone(),
                                                ));
                                                // Store the cell back to the local slot so other closures share it
                                                self.stack
                                                    .set(base + slot as usize, cell_val.clone())?;
                                                captures.push(cell_val);
                                            }
                                        } else {
                                            // Wrap in a new heap cell
                                            let cell = HeapCell::new(val);
                                            let cell_val =
                                                KlujurVal::custom(HeapCellWrapper(cell.clone()));
                                            // Store the cell back to the local slot so other closures share it
                                            self.stack
                                                .set(base + slot as usize, cell_val.clone())?;
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

                // Additional built-in operations
                OpCode::Get => {
                    let key = self.stack.pop()?;
                    let coll = self.stack.pop()?;
                    let result = match &coll {
                        KlujurVal::Map(map, _) => map.get(&key).cloned().unwrap_or(KlujurVal::Nil),
                        KlujurVal::Vector(items, _) => {
                            if let KlujurVal::Int(idx) = key {
                                if idx >= 0 && (idx as usize) < items.len() {
                                    items[idx as usize].clone()
                                } else {
                                    KlujurVal::Nil
                                }
                            } else {
                                KlujurVal::Nil
                            }
                        }
                        KlujurVal::Set(set, _) => {
                            if set.contains(&key) {
                                key
                            } else {
                                KlujurVal::Nil
                            }
                        }
                        KlujurVal::Nil => KlujurVal::Nil,
                        _ => KlujurVal::Nil,
                    };
                    self.stack.push(result);
                }
                OpCode::GetDefault => {
                    let default = self.stack.pop()?;
                    let key = self.stack.pop()?;
                    let coll = self.stack.pop()?;
                    let result = match &coll {
                        KlujurVal::Map(map, _) => map.get(&key).cloned().unwrap_or(default),
                        KlujurVal::Vector(items, _) => {
                            if let KlujurVal::Int(idx) = key {
                                if idx >= 0 && (idx as usize) < items.len() {
                                    items[idx as usize].clone()
                                } else {
                                    default
                                }
                            } else {
                                default
                            }
                        }
                        KlujurVal::Set(set, _) => {
                            if set.contains(&key) {
                                key
                            } else {
                                default
                            }
                        }
                        KlujurVal::Nil => default,
                        _ => default,
                    };
                    self.stack.push(result);
                }
                OpCode::Assoc => {
                    let val = self.stack.pop()?;
                    let key = self.stack.pop()?;
                    let coll = self.stack.pop()?;
                    let result = match coll {
                        KlujurVal::Map(mut map, meta) => {
                            map.insert(key, val);
                            KlujurVal::Map(map, meta)
                        }
                        KlujurVal::Vector(mut items, meta) => {
                            if let KlujurVal::Int(idx) = key {
                                if idx >= 0 && (idx as usize) <= items.len() {
                                    if (idx as usize) == items.len() {
                                        // Append at end
                                        items.push_back(val);
                                    } else {
                                        // Replace at index
                                        items.set(idx as usize, val);
                                    }
                                    KlujurVal::Vector(items, meta)
                                } else {
                                    return Err(RuntimeError::Internal(format!(
                                        "Index {} out of bounds for vector of length {}",
                                        idx,
                                        items.len()
                                    )));
                                }
                            } else {
                                return Err(RuntimeError::TypeError {
                                    expected: "integer".into(),
                                    got: type_name(&key).into(),
                                });
                            }
                        }
                        KlujurVal::Nil => {
                            // assoc on nil creates a map
                            let mut map = im::OrdMap::new();
                            map.insert(key, val);
                            KlujurVal::Map(map, None)
                        }
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "map or vector".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(result);
                }
                OpCode::Conj => {
                    let val = self.stack.pop()?;
                    let coll = self.stack.pop()?;
                    let result = match coll {
                        KlujurVal::List(mut items, meta) => {
                            items.push_front(val);
                            KlujurVal::List(items, meta)
                        }
                        KlujurVal::Vector(mut items, meta) => {
                            items.push_back(val);
                            KlujurVal::Vector(items, meta)
                        }
                        KlujurVal::Set(mut set, meta) => {
                            set.insert(val);
                            KlujurVal::Set(set, meta)
                        }
                        KlujurVal::Nil => KlujurVal::list(vec![val]),
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "collection".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(result);
                }
                OpCode::Count => {
                    let coll = self.stack.pop()?;
                    let count = match &coll {
                        KlujurVal::Nil => 0,
                        KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                            items.len() as i64
                        }
                        KlujurVal::Map(map, _) => map.len() as i64,
                        KlujurVal::Set(set, _) => set.len() as i64,
                        KlujurVal::String(s) => s.chars().count() as i64,
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "collection".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(KlujurVal::Int(count));
                }
                OpCode::Next => {
                    let coll = self.stack.pop()?;
                    let next = match &coll {
                        KlujurVal::List(items, _) => {
                            if items.len() <= 1 {
                                KlujurVal::Nil
                            } else {
                                KlujurVal::list(items.iter().skip(1).cloned().collect())
                            }
                        }
                        KlujurVal::Vector(items, _) => {
                            if items.len() <= 1 {
                                KlujurVal::Nil
                            } else {
                                KlujurVal::list(items.iter().skip(1).cloned().collect())
                            }
                        }
                        KlujurVal::Nil => KlujurVal::Nil,
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "sequence".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                    };
                    self.stack.push(next);
                }
                OpCode::Nth => {
                    let idx = self.stack.pop()?;
                    let coll = self.stack.pop()?;
                    let result = match (&coll, &idx) {
                        (KlujurVal::Vector(items, _), KlujurVal::Int(i)) => {
                            if *i >= 0 && (*i as usize) < items.len() {
                                items[*i as usize].clone()
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "Index {} out of bounds for vector of length {}",
                                    i,
                                    items.len()
                                )));
                            }
                        }
                        (KlujurVal::List(items, _), KlujurVal::Int(i)) => {
                            if *i >= 0 && (*i as usize) < items.len() {
                                items[*i as usize].clone()
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "Index {} out of bounds for list of length {}",
                                    i,
                                    items.len()
                                )));
                            }
                        }
                        (KlujurVal::String(s), KlujurVal::Int(i)) => {
                            if *i >= 0 {
                                s.chars().nth(*i as usize).map(KlujurVal::Char).ok_or_else(
                                    || {
                                        RuntimeError::Internal(format!(
                                            "Index {} out of bounds for string of length {}",
                                            i,
                                            s.chars().count()
                                        ))
                                    },
                                )?
                            } else {
                                return Err(RuntimeError::Internal(format!(
                                    "Index {} out of bounds",
                                    i
                                )));
                            }
                        }
                        (_, KlujurVal::Int(_)) => {
                            return Err(RuntimeError::TypeError {
                                expected: "indexed collection".into(),
                                got: type_name(&coll).into(),
                            });
                        }
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "integer".into(),
                                got: type_name(&idx).into(),
                            });
                        }
                    };
                    self.stack.push(result);
                }
                OpCode::NilP => {
                    let val = self.stack.pop()?;
                    self.stack
                        .push(KlujurVal::Bool(matches!(val, KlujurVal::Nil)));
                }
                OpCode::EmptyP => {
                    let val = self.stack.pop()?;
                    let is_empty = match &val {
                        KlujurVal::Nil => true,
                        KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => items.is_empty(),
                        KlujurVal::Map(map, _) => map.is_empty(),
                        KlujurVal::Set(set, _) => set.is_empty(),
                        KlujurVal::String(s) => s.is_empty(),
                        _ => false,
                    };
                    self.stack.push(KlujurVal::Bool(is_empty));
                }
                OpCode::Inc => {
                    let val = self.stack.pop()?;
                    match val {
                        KlujurVal::Int(n) => {
                            self.stack
                                .push(KlujurVal::Int(n.checked_add(1).ok_or_else(|| {
                                    RuntimeError::Internal("Integer overflow in inc".into())
                                })?));
                        }
                        KlujurVal::Float(n) => {
                            self.stack.push(KlujurVal::Float(n + 1.0));
                        }
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "number".into(),
                                got: type_name(&val).into(),
                            });
                        }
                    }
                }
                OpCode::Dec => {
                    let val = self.stack.pop()?;
                    match val {
                        KlujurVal::Int(n) => {
                            self.stack
                                .push(KlujurVal::Int(n.checked_sub(1).ok_or_else(|| {
                                    RuntimeError::Internal("Integer overflow in dec".into())
                                })?));
                        }
                        KlujurVal::Float(n) => {
                            self.stack.push(KlujurVal::Float(n - 1.0));
                        }
                        _ => {
                            return Err(RuntimeError::TypeError {
                                expected: "number".into(),
                                got: type_name(&val).into(),
                            });
                        }
                    }
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
            let is_multi_arity = bytecode_fn.is_multi_arity();

            // Multi-arity functions handle their own arity dispatch via ArityDispatch opcode
            // Skip arity checking and rest handling for them
            if !is_multi_arity {
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
        // Collect arguments from the stack
        let args: Vec<KlujurVal> = (0..argc)
            .map(|i| self.stack.get(fn_index + 1 + i))
            .collect::<Result<Vec<_>>>()?;

        // Call the external function
        let result = call_external_fn(&callee, &args).map_err(RuntimeError::Internal)?;

        // Pop the function and arguments, then push the result
        self.stack.truncate(fn_index);
        self.stack.push(result);
        Ok(())
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
            let is_multi_arity = bytecode_fn.is_multi_arity();

            // Multi-arity functions handle their own arity dispatch via ArityDispatch opcode
            if !is_multi_arity {
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
            }

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
            frame.argc = argc as u8;
            // cleanup_base stays the same

            return Ok(());
        }

        // Not a bytecode function - handle as external call (no TCO benefit for external)
        // Collect arguments from the stack
        let args: Vec<KlujurVal> = (0..argc)
            .map(|i| self.stack.get(fn_index + 1 + i))
            .collect::<Result<Vec<_>>>()?;

        // Call the external function
        let result = call_external_fn(&callee, &args).map_err(RuntimeError::Internal)?;

        // Pop the function and arguments, then push the result
        self.stack.truncate(fn_index);
        self.stack.push(result);
        Ok(())
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
