// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Bytecode emission trait for compilers.
//!
//! This trait defines the common interface for bytecode emission,
//! enabling code reuse between the top-level Compiler and FunctionCompiler.

use klujur_parser::value::KlujurVal;

use crate::opcode::OpCode;

use super::types::Result;

/// Trait for types that can emit bytecode.
///
/// Both `Compiler` and `FunctionCompiler` implement this trait,
/// allowing shared compilation logic for special forms.
pub trait BytecodeEmitter {
    /// Emit an opcode.
    fn emit(&mut self, op: OpCode);

    /// Emit a constant and return its index.
    fn emit_constant(&mut self, value: KlujurVal) -> Result<()>;

    /// Emit a jump instruction and return its offset for patching.
    fn emit_jump(&mut self, op: OpCode) -> usize;

    /// Patch a jump instruction at the given offset.
    fn patch_jump(&mut self, offset: usize);

    /// Compile an expression.
    fn compile_expr(&mut self, expr: &KlujurVal) -> Result<()>;
}

/// Control flow compilation using the BytecodeEmitter trait.
///
/// These functions can be used by any compiler that implements BytecodeEmitter.
pub mod control {
    use super::*;

    /// Compile `(if test then else?)` form.
    pub fn compile_if<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        emitter.compile_expr(&args[0])?;

        // Jump to else if false
        let else_jump = emitter.emit_jump(OpCode::PopJumpIfFalse(0));

        // Compile then branch
        if args.len() > 1 {
            emitter.compile_expr(&args[1])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        // Jump over else
        let end_jump = emitter.emit_jump(OpCode::Jump(0));

        // Patch else jump
        emitter.patch_jump(else_jump);

        // Compile else branch
        if args.len() > 2 {
            emitter.compile_expr(&args[2])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        // Patch end jump
        emitter.patch_jump(end_jump);
        Ok(())
    }

    /// Compile `(do body...)` form.
    pub fn compile_do<E: BytecodeEmitter>(emitter: &mut E, body: &[KlujurVal]) -> Result<()> {
        if body.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile all but last, discarding results
        for expr in &body[..body.len() - 1] {
            emitter.compile_expr(expr)?;
            emitter.emit(OpCode::Pop);
        }

        // Last expression is the result
        emitter.compile_expr(&body[body.len() - 1])
    }

    /// Compile `(when test body...)` form.
    pub fn compile_when<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        emitter.compile_expr(&args[0])?;
        let else_jump = emitter.emit_jump(OpCode::PopJumpIfFalse(0));

        // Compile body (as do block)
        if args.len() > 1 {
            compile_do(emitter, &args[1..])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        let end_jump = emitter.emit_jump(OpCode::Jump(0));
        emitter.patch_jump(else_jump);
        emitter.emit(OpCode::Nil);
        emitter.patch_jump(end_jump);
        Ok(())
    }

    /// Compile `(when-not test body...)` form.
    pub fn compile_when_not<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        emitter.compile_expr(&args[0])?;
        let then_jump = emitter.emit_jump(OpCode::PopJumpIfTrue(0));

        // Compile body (as do block) - executes when test is falsey
        if args.len() > 1 {
            compile_do(emitter, &args[1..])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        let end_jump = emitter.emit_jump(OpCode::Jump(0));
        emitter.patch_jump(then_jump);
        emitter.emit(OpCode::Nil);
        emitter.patch_jump(end_jump);
        Ok(())
    }

    /// Compile `(if-not test then else?)` form.
    pub fn compile_if_not<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        emitter.compile_expr(&args[0])?;

        // Jump to else if true (inverted from regular if)
        let else_jump = emitter.emit_jump(OpCode::PopJumpIfTrue(0));

        // Compile then branch (executes when test is false)
        if args.len() > 1 {
            emitter.compile_expr(&args[1])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        // Jump over else
        let end_jump = emitter.emit_jump(OpCode::Jump(0));
        emitter.patch_jump(else_jump);

        // Compile else branch (executes when test is true)
        if args.len() > 2 {
            emitter.compile_expr(&args[2])?;
        } else {
            emitter.emit(OpCode::Nil);
        }

        emitter.patch_jump(end_jump);
        Ok(())
    }

    /// Compile `(and args...)` form with short-circuit evaluation.
    pub fn compile_and<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::True);
            return Ok(());
        }

        if args.len() == 1 {
            return emitter.compile_expr(&args[0]);
        }

        let mut end_jumps = Vec::new();

        // Compile all but last
        for expr in &args[..args.len() - 1] {
            emitter.compile_expr(expr)?;
            emitter.emit(OpCode::Dup);
            end_jumps.push(emitter.emit_jump(OpCode::JumpIfFalse(0)));
            emitter.emit(OpCode::Pop);
        }

        // Compile last expression
        emitter.compile_expr(&args[args.len() - 1])?;

        // Patch all end jumps
        for jump in end_jumps {
            emitter.patch_jump(jump);
        }

        Ok(())
    }

    /// Compile `(or args...)` form with short-circuit evaluation.
    pub fn compile_or<E: BytecodeEmitter>(emitter: &mut E, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            emitter.emit(OpCode::Nil);
            return Ok(());
        }

        if args.len() == 1 {
            return emitter.compile_expr(&args[0]);
        }

        let mut end_jumps = Vec::new();

        // Compile all but last
        for expr in &args[..args.len() - 1] {
            emitter.compile_expr(expr)?;
            emitter.emit(OpCode::Dup);
            end_jumps.push(emitter.emit_jump(OpCode::JumpIfTrue(0)));
            emitter.emit(OpCode::Pop);
        }

        // Compile last expression
        emitter.compile_expr(&args[args.len() - 1])?;

        // Patch all end jumps
        for jump in end_jumps {
            emitter.patch_jump(jump);
        }

        Ok(())
    }
}
