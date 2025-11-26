// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Stack-based virtual machine for executing Klujur bytecode.

pub mod error;
pub mod frame;
pub mod handlers;
pub mod stack;

use std::cell::RefCell;
use std::rc::Rc;

use klujur_parser::value::KlujurVal;

use crate::chunk::{BytecodeFn, BytecodeFnWrapper, Chunk};
use crate::opcode::OpCode;
use crate::utils::is_falsy;

pub use error::{Result, RuntimeError};
pub use frame::CallFrame;
pub use handlers::control::ControlFlow;
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

/// The Klujur virtual machine.
pub struct VM {
    /// Value stack.
    stack: ValueStack,

    /// Call frame stack.
    frames: Vec<CallFrame>,

    /// Chunks being executed (index 0 is the main chunk).
    /// Uses Rc<Chunk> to avoid cloning chunks on every function call.
    chunks: Vec<Rc<Chunk>>,

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
        // Store the chunk (wrap in Rc for sharing)
        self.chunks.push(Rc::new(chunk));
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

        // Add the function's chunk to our chunks list (Rc::clone is cheap)
        let chunk = bytecode_fn.chunk();
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
                // Constants & Stack - handled inline (simple operations)
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
                OpCode::Nil => self.stack.push(KlujurVal::Nil),
                OpCode::True => self.stack.push(KlujurVal::Bool(true)),
                OpCode::False => self.stack.push(KlujurVal::Bool(false)),
                OpCode::Not => {
                    let val = self.stack.pop()?;
                    self.stack.push(KlujurVal::Bool(is_falsy(&val)));
                }

                // Variables - delegated to handler
                OpCode::LoadLocal(_)
                | OpCode::StoreLocal(_)
                | OpCode::LoadGlobal(_)
                | OpCode::DefGlobal(_)
                | OpCode::LoadCapture(_) => {
                    self.execute_variables(op)?;
                }

                // Heap cells - delegated to handler
                OpCode::Alloc
                | OpCode::LoadHeap(_)
                | OpCode::StoreHeap(_)
                | OpCode::LoadLocalHeap(_)
                | OpCode::StoreLocalHeap(_) => {
                    self.execute_heap(op)?;
                }

                // Control flow - delegated to handler
                OpCode::Jump(_)
                | OpCode::JumpIfFalse(_)
                | OpCode::JumpIfTrue(_)
                | OpCode::PopJumpIfFalse(_)
                | OpCode::PopJumpIfTrue(_)
                | OpCode::Call(_)
                | OpCode::TailCall(_)
                | OpCode::Return
                | OpCode::CheckArity(_)
                | OpCode::CheckArityAtLeast(_)
                | OpCode::ArityDispatch(_)
                | OpCode::ArityEntry { .. }
                | OpCode::Closure(_)
                | OpCode::CaptureLocal(_)
                | OpCode::CaptureUpvalue(_)
                | OpCode::CaptureHeapLocal(_)
                | OpCode::CaptureHeapUpvalue(_) => match self.execute_control(op)? {
                    ControlFlow::Continue => {}
                    ControlFlow::Return(result) => return Ok(result),
                },

                // Arithmetic - delegated to handler
                OpCode::Add
                | OpCode::Sub
                | OpCode::Mul
                | OpCode::Div
                | OpCode::Inc
                | OpCode::Dec => {
                    self.execute_arithmetic(op)?;
                }

                // Comparison - handled inline (simple) or via handler
                OpCode::Eq => {
                    let b = self.stack.pop()?;
                    let a = self.stack.pop()?;
                    self.stack.push(KlujurVal::Bool(a == b));
                }
                OpCode::Lt => self.comparison_op(|a, b| a < b, |a, b| a < b, "<")?,
                OpCode::Gt => self.comparison_op(|a, b| a > b, |a, b| a > b, ">")?,
                OpCode::Le => self.comparison_op(|a, b| a <= b, |a, b| a <= b, "<=")?,
                OpCode::Ge => self.comparison_op(|a, b| a >= b, |a, b| a >= b, ">=")?,

                // Sequence operations - delegated to handler
                OpCode::Cons
                | OpCode::First
                | OpCode::Rest
                | OpCode::Next
                | OpCode::NilP
                | OpCode::EmptyP => {
                    self.execute_sequences(op)?;
                }

                // Collection operations - delegated to handler
                OpCode::Get
                | OpCode::GetDefault
                | OpCode::Assoc
                | OpCode::Conj
                | OpCode::Count
                | OpCode::Nth
                | OpCode::BuildVector(_)
                | OpCode::BuildMap(_)
                | OpCode::BuildSet(_) => {
                    self.execute_collections(op)?;
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

    pub(crate) fn jump(&mut self, offset: i16) -> Result<()> {
        let frame = self.frame_mut();
        let new_ip = frame.ip as i64 + offset as i64;
        if new_ip < 0 {
            return Err(RuntimeError::Internal(
                "Jump instruction resulted in negative instruction pointer".into(),
            ));
        }
        frame.ip = new_ip as usize;
        Ok(())
    }
}

impl Default for VM {
    fn default() -> Self {
        Self::new()
    }
}
