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
    // Function Calls
    // =========================================================================
    /// Call function with n arguments. Function is at stack[sp - n - 1].
    Call(u8),

    /// Tail call: reuse current frame. Function is at stack[sp - n - 1].
    TailCall(u8),

    /// Return from function: pop return value and restore caller's frame.
    Return,

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
            | OpCode::Nil
            | OpCode::True
            | OpCode::False => 1,

            // Pop 1
            OpCode::Pop | OpCode::DefGlobal(_) | OpCode::StoreLocal(_) | OpCode::StoreHeap(_) => -1,

            // Neutral (pop 1, push 1)
            OpCode::Alloc | OpCode::First | OpCode::Rest | OpCode::Not => 0,

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
            | OpCode::Cons => -1,

            // Control flow (no stack effect on their own)
            OpCode::Jump(_) | OpCode::JumpIfFalse(_) | OpCode::JumpIfTrue(_) => 0,

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
