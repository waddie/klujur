// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode chunks and function prototypes.

use std::rc::Rc;

use klujur_parser::Symbol;
use klujur_parser::value::KlujurVal;

use crate::OpCode;

/// Debug information for a single instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LineInfo {
    /// Source line number (1-indexed).
    pub line: u32,
    /// Source column number (1-indexed).
    pub column: u32,
}

impl LineInfo {
    /// Create a new LineInfo.
    pub fn new(line: u32, column: u32) -> Self {
        Self { line, column }
    }
}

/// A chunk of bytecode with its constant pool and debug information.
#[derive(Debug, Clone)]
pub struct Chunk {
    /// The bytecode instructions.
    pub code: Vec<OpCode>,

    /// Constant pool: literals, symbols, and nested function prototypes.
    pub constants: Vec<KlujurVal>,

    /// Debug info: source location for each instruction.
    /// Same length as `code`.
    pub lines: Vec<LineInfo>,
}

impl Chunk {
    /// Create a new empty chunk.
    pub fn new() -> Self {
        Self {
            code: Vec::new(),
            constants: Vec::new(),
            lines: Vec::new(),
        }
    }

    /// Emit an instruction with source location.
    pub fn emit(&mut self, op: OpCode, line_info: LineInfo) {
        self.code.push(op);
        self.lines.push(line_info);
    }

    /// Emit an instruction without source location (uses default).
    pub fn emit_op(&mut self, op: OpCode) {
        self.emit(op, LineInfo::default());
    }

    /// Add a constant to the pool and return its index.
    ///
    /// Returns `None` if the constant pool is full (> u16::MAX entries).
    pub fn add_constant(&mut self, value: KlujurVal) -> Option<u16> {
        // Check for existing constant to deduplicate
        for (i, existing) in self.constants.iter().enumerate() {
            if Self::constants_equal(existing, &value) {
                return Some(i as u16);
            }
        }

        let idx = self.constants.len();
        if idx > u16::MAX as usize {
            return None;
        }
        self.constants.push(value);
        Some(idx as u16)
    }

    /// Check if two constants are equal for deduplication purposes.
    /// Functions are never deduplicated.
    fn constants_equal(a: &KlujurVal, b: &KlujurVal) -> bool {
        match (a, b) {
            (KlujurVal::Nil, KlujurVal::Nil) => true,
            (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a == b,
            (KlujurVal::Int(a), KlujurVal::Int(b)) => a == b,
            (KlujurVal::Float(a), KlujurVal::Float(b)) => a.to_bits() == b.to_bits(),
            (KlujurVal::String(a), KlujurVal::String(b)) => a == b,
            (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a == b,
            (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a == b,
            _ => false,
        }
    }

    /// Get the current instruction offset (for jump patching).
    pub fn current_offset(&self) -> usize {
        self.code.len()
    }

    /// Patch a jump instruction at the given offset to jump to the current position.
    pub fn patch_jump(&mut self, offset: usize) {
        let jump_distance = self.code.len() as i16 - offset as i16 - 1;
        match &mut self.code[offset] {
            OpCode::Jump(target)
            | OpCode::JumpIfFalse(target)
            | OpCode::JumpIfTrue(target)
            | OpCode::PopJumpIfFalse(target)
            | OpCode::PopJumpIfTrue(target) => {
                *target = jump_distance;
            }
            other => debug_assert!(false, "patch_jump called on non-jump: {:?}", other),
        }
    }

    /// Get the source location for an instruction at the given offset.
    pub fn get_line_info(&self, offset: usize) -> Option<LineInfo> {
        self.lines.get(offset).copied()
    }
}

impl Default for Chunk {
    fn default() -> Self {
        Self::new()
    }
}

/// A function prototype: the compiled representation of a function before closure creation.
#[derive(Debug, Clone)]
pub struct FunctionPrototype {
    /// Function name (for debugging and self-recursion).
    pub name: Option<Symbol>,

    /// Number of required parameters (minimum for multi-arity).
    pub arity: u8,

    /// Whether this function has a rest parameter.
    pub has_rest: bool,

    /// Whether this is a multi-arity function (handles its own arity dispatch).
    pub is_multi_arity: bool,

    /// The compiled bytecode for this function's body.
    /// Wrapped in Rc for efficient sharing - chunks are never mutated after compilation.
    pub chunk: Rc<Chunk>,

    /// Number of captured variables (upvalues).
    pub upvalue_count: u16,

    /// Number of local slots needed (parameters + let bindings).
    pub local_count: u16,
}

impl FunctionPrototype {
    /// Create a new function prototype.
    pub fn new(name: Option<Symbol>, arity: u8, has_rest: bool) -> Self {
        Self {
            name,
            arity,
            has_rest,
            is_multi_arity: false,
            chunk: Rc::new(Chunk::new()),
            upvalue_count: 0,
            local_count: 0,
        }
    }

    /// Create a new multi-arity function prototype.
    pub fn new_multi_arity(name: Option<Symbol>, min_arity: u8) -> Self {
        Self {
            name,
            arity: min_arity,
            has_rest: false,
            is_multi_arity: true,
            chunk: Rc::new(Chunk::new()),
            upvalue_count: 0,
            local_count: 0,
        }
    }
}

/// Information about a captured variable (upvalue).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UpvalueInfo {
    /// Index in the enclosing scope.
    pub index: u16,

    /// Whether this captures from the immediate parent's locals (true)
    /// or from the parent's upvalues (false).
    pub is_local: bool,

    /// Whether this variable needs heap allocation (is mutated via set!).
    pub is_mutable: bool,
}

impl UpvalueInfo {
    /// Create info for capturing a local variable.
    pub fn local(index: u16, is_mutable: bool) -> Self {
        Self {
            index,
            is_local: true,
            is_mutable,
        }
    }

    /// Create info for capturing from parent's upvalues.
    pub fn upvalue(index: u16, is_mutable: bool) -> Self {
        Self {
            index,
            is_local: false,
            is_mutable,
        }
    }
}

/// A compiled bytecode function ready for execution.
///
/// This is the runtime representation of a function, containing the compiled
/// bytecode and any captured values from the enclosing scope.
#[derive(Debug, Clone)]
pub struct BytecodeFn {
    /// The function prototype (shared between all closures of this function).
    pub prototype: Rc<FunctionPrototype>,

    /// Captured values from enclosing scopes.
    /// These are the actual values (for immutable captures) or heap cell
    /// references (for mutable captures).
    pub captures: Vec<KlujurVal>,
}

impl BytecodeFn {
    /// Create a new bytecode function with no captures.
    pub fn new(prototype: Rc<FunctionPrototype>) -> Self {
        Self {
            prototype,
            captures: Vec::new(),
        }
    }

    /// Create a new bytecode function with captures.
    pub fn with_captures(prototype: Rc<FunctionPrototype>, captures: Vec<KlujurVal>) -> Self {
        Self {
            prototype,
            captures,
        }
    }

    /// Get the function name (if any).
    pub fn name(&self) -> Option<&Symbol> {
        self.prototype.name.as_ref()
    }

    /// Get the function arity (number of required parameters).
    pub fn arity(&self) -> u8 {
        self.prototype.arity
    }

    /// Check if this function has a rest parameter.
    pub fn has_rest(&self) -> bool {
        self.prototype.has_rest
    }

    /// Check if this is a multi-arity function.
    pub fn is_multi_arity(&self) -> bool {
        self.prototype.is_multi_arity
    }

    /// Get the bytecode chunk (shared reference).
    pub fn chunk(&self) -> Rc<Chunk> {
        Rc::clone(&self.prototype.chunk)
    }
}

/// Wrapper for BytecodeFn to store in KlujurVal::Custom.
#[derive(Debug, Clone)]
pub struct BytecodeFnWrapper(pub Rc<BytecodeFn>);

impl klujur_parser::value::CustomType for BytecodeFnWrapper {
    fn type_name(&self) -> &'static str {
        "BytecodeFn"
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#<fn {}>",
            self.0.name().map(|s| s.name()).unwrap_or("anonymous")
        )
    }
}

/// A heap cell for mutable captured variables.
///
/// When a variable is both captured by a closure AND mutated via `set!`,
/// it must be allocated on the heap so changes are visible across all
/// closures that captured it.
#[derive(Debug, Clone)]
pub struct HeapCell(pub Rc<std::cell::RefCell<KlujurVal>>);

impl HeapCell {
    /// Create a new heap cell containing the given value.
    pub fn new(val: KlujurVal) -> Self {
        Self(Rc::new(std::cell::RefCell::new(val)))
    }

    /// Get the value from the heap cell.
    pub fn get(&self) -> KlujurVal {
        self.0.borrow().clone()
    }

    /// Set the value in the heap cell.
    pub fn set(&self, val: KlujurVal) {
        *self.0.borrow_mut() = val;
    }
}

/// Wrapper for HeapCell to store in KlujurVal::Custom.
#[derive(Debug, Clone)]
pub struct HeapCellWrapper(pub HeapCell);

impl klujur_parser::value::CustomType for HeapCellWrapper {
    fn type_name(&self) -> &'static str {
        "HeapCell"
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#<heap-cell {:?}>", self.0.get())
    }
}
