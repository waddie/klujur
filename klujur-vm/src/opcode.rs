// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode instruction definitions.

/// Bytecode instructions for the Klujur VM.
///
/// Instructions operate on a value stack. Most instructions push or pop values
/// from the stack. Jump offsets are relative to the current instruction pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    // =========================================================================
    // Constants & Stack
    // =========================================================================
    /// Push constant from constant pool onto stack.
    Const(u16),

    /// Pop top value from stack.
    Pop,

    /// Duplicate top value on stack.
    Dup,

    // =========================================================================
    // Variables (stack-relative offsets)
    // =========================================================================
    /// Load local variable: push stack[frame_base + n].
    LoadLocal(u16),

    /// Store to local variable: stack[frame_base + n] = pop().
    StoreLocal(u16),

    /// Load captured variable: push captures[n].
    LoadCapture(u16),

    /// Load global variable: look up symbol (in constants[n]) in namespace.
    LoadGlobal(u16),

    /// Define global variable: intern symbol (in constants[n]) with pop().
    DefGlobal(u16),

    // =========================================================================
    // Heap Cells (for mutable captures)
    // =========================================================================
    /// Allocate heap cell containing top of stack (replaces top with cell reference).
    Alloc,

    /// Load from heap cell: push value from heap cell in captures[n].
    LoadHeap(u16),

    /// Store to heap cell: set value in heap cell in captures[n] to pop().
    StoreHeap(u16),

    /// Load from boxed local: read heap cell from local slot n, push its value.
    LoadLocalHeap(u16),

    /// Store to boxed local: read heap cell from local slot n, store popped value into it.
    StoreLocalHeap(u16),

    // =========================================================================
    // Control Flow
    // =========================================================================
    /// Unconditional relative jump.
    Jump(i16),

    /// Jump if top of stack is falsy (nil or false). Does not pop.
    JumpIfFalse(i16),

    /// Jump if top of stack is truthy (not nil or false). Does not pop.
    JumpIfTrue(i16),

    /// Pop and jump if falsy.
    PopJumpIfFalse(i16),

    /// Pop and jump if truthy.
    PopJumpIfTrue(i16),

    // =========================================================================
    // Function Calls & Arity
    // =========================================================================
    /// Call function with n arguments. Function is at stack[sp - n - 1].
    Call(u8),

    /// Tail call: reuse current frame. Function is at stack[sp - n - 1].
    TailCall(u8),

    /// Return from function: pop return value and restore caller's frame.
    Return,

    /// Check that argc equals expected arity, error otherwise.
    /// argc is read from the call site info stored in the frame.
    CheckArity(u8),

    /// Check that argc >= minimum arity (for variadic functions).
    CheckArityAtLeast(u8),

    /// Multi-arity dispatch: jump to the correct arity handler.
    /// The u8 is the number of arity entries in the dispatch table.
    /// Each entry is encoded as: (arity: u8, has_rest: bool, offset: i16).
    /// Entries are read as following opcodes: ArityEntry(u8, bool, i16).
    ArityDispatch(u8),

    /// Arity dispatch table entry: (fixed_arity, has_rest, jump_offset).
    /// Used only within ArityDispatch block.
    ArityEntry {
        arity: u8,
        has_rest: bool,
        offset: i16,
    },

    // =========================================================================
    // Closure Construction
    // =========================================================================
    /// Create closure from function prototype in constants[n].
    /// Following instructions specify captures.
    Closure(u16),

    /// Capture local variable: add stack[frame_base + n] to closure being built.
    CaptureLocal(u16),

    /// Capture upvalue: add parent's captures[n] to closure being built.
    CaptureUpvalue(u16),

    /// Capture heap cell from local: allocate cell for stack[frame_base + n].
    CaptureHeapLocal(u16),

    /// Capture heap cell from parent: add parent's heap cell captures[n].
    CaptureHeapUpvalue(u16),

    // =========================================================================
    // Built-in Operations (hot-path optimisations)
    // =========================================================================
    /// Addition: push pop() + pop().
    Add,

    /// Subtraction: push a - b where b = pop(), a = pop().
    Sub,

    /// Multiplication: push pop() * pop().
    Mul,

    /// Division: push a / b where b = pop(), a = pop().
    Div,

    /// Equality: push pop() == pop().
    Eq,

    /// Less than: push a < b where b = pop(), a = pop().
    Lt,

    /// Greater than: push a > b where b = pop(), a = pop().
    Gt,

    /// Less than or equal: push a <= b where b = pop(), a = pop().
    Le,

    /// Greater than or equal: push a >= b where b = pop(), a = pop().
    Ge,

    /// Cons: push (cons a b) where b = pop(), a = pop().
    Cons,

    /// First: push (first pop()).
    First,

    /// Rest: push (rest pop()).
    Rest,

    /// Push nil.
    Nil,

    /// Push true.
    True,

    /// Push false.
    False,

    /// Negate: push (not pop()).
    Not,

    // =========================================================================
    // Additional Built-in Operations
    // =========================================================================
    /// Get: push (get coll key) where key = pop(), coll = pop().
    Get,

    /// Get with default: push (get coll key default) where default = pop(), key = pop(), coll = pop().
    GetDefault,

    /// Assoc: push (assoc coll k v) where v = pop(), k = pop(), coll = pop().
    Assoc,

    /// Conj: push (conj coll val) where val = pop(), coll = pop().
    Conj,

    /// Count: push (count pop()).
    Count,

    /// Next: push (next pop()) - like rest but returns nil for empty.
    Next,

    /// Nth: push (nth coll idx) where idx = pop(), coll = pop().
    Nth,

    /// Nil predicate: push (nil? pop()).
    NilP,

    /// Empty predicate: push (empty? pop()).
    EmptyP,

    /// Increment: push (inc pop()).
    Inc,

    /// Decrement: push (dec pop()).
    Dec,
}

impl OpCode {
    /// Returns true if this instruction transfers control (jump, call, return).
    #[inline]
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            OpCode::Jump(_)
                | OpCode::JumpIfFalse(_)
                | OpCode::JumpIfTrue(_)
                | OpCode::PopJumpIfFalse(_)
                | OpCode::PopJumpIfTrue(_)
                | OpCode::Call(_)
                | OpCode::TailCall(_)
                | OpCode::Return
                | OpCode::ArityDispatch(_)
                | OpCode::ArityEntry { .. }
        )
    }

    /// Returns the stack effect of this instruction (positive = push, negative = pop).
    /// Returns None for instructions with variable stack effects (Call, TailCall).
    #[inline]
    pub fn stack_effect(&self) -> Option<i8> {
        Some(match self {
            // Push 1
            OpCode::Const(_)
            | OpCode::Dup
            | OpCode::LoadLocal(_)
            | OpCode::LoadCapture(_)
            | OpCode::LoadGlobal(_)
            | OpCode::LoadHeap(_)
            | OpCode::LoadLocalHeap(_)
            | OpCode::Nil
            | OpCode::True
            | OpCode::False => 1,

            // Pop 1
            OpCode::Pop
            | OpCode::DefGlobal(_)
            | OpCode::StoreLocal(_)
            | OpCode::StoreHeap(_)
            | OpCode::StoreLocalHeap(_) => -1,

            // Neutral (pop 1, push 1)
            OpCode::Alloc
            | OpCode::First
            | OpCode::Rest
            | OpCode::Not
            | OpCode::Count
            | OpCode::Next
            | OpCode::NilP
            | OpCode::EmptyP
            | OpCode::Inc
            | OpCode::Dec => 0,

            // Pop 2, push 1
            OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Div
            | OpCode::Eq
            | OpCode::Lt
            | OpCode::Gt
            | OpCode::Le
            | OpCode::Ge
            | OpCode::Cons
            | OpCode::Get
            | OpCode::Nth => -1,

            // Pop 3, push 1
            OpCode::GetDefault | OpCode::Assoc | OpCode::Conj => -2,

            // Control flow (no stack effect on their own)
            OpCode::Jump(_)
            | OpCode::JumpIfFalse(_)
            | OpCode::JumpIfTrue(_)
            | OpCode::CheckArity(_)
            | OpCode::CheckArityAtLeast(_)
            | OpCode::ArityDispatch(_)
            | OpCode::ArityEntry { .. } => 0,

            // Pop and jump
            OpCode::PopJumpIfFalse(_) | OpCode::PopJumpIfTrue(_) => -1,

            // Return pops 1 but frame change makes this complex
            OpCode::Return => 0,

            // Variable effect
            OpCode::Call(_) | OpCode::TailCall(_) => return None,

            // Closure construction is complex (depends on capture count)
            OpCode::Closure(_)
            | OpCode::CaptureLocal(_)
            | OpCode::CaptureUpvalue(_)
            | OpCode::CaptureHeapLocal(_)
            | OpCode::CaptureHeapUpvalue(_) => return None,
        })
    }
}
