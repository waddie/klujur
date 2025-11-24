// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Code generation: transforms analysed AST to bytecode.

use std::any::Any;
use std::collections::HashMap;

use klujur_parser::Symbol;
use klujur_parser::value::{CustomType, KlujurVal};

use crate::chunk::{Chunk, FunctionPrototype, LineInfo};
use crate::opcode::OpCode;

use super::analysis::AnalysisResult;

/// Error during compilation.
#[derive(Debug, Clone)]
pub enum CompileError {
    /// Constant pool overflow.
    TooManyConstants,
    /// Too many local variables.
    TooManyLocals,
    /// Invalid syntax.
    Syntax(String),
    /// Recur outside loop.
    RecurOutsideLoop,
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::TooManyConstants => write!(f, "Too many constants in function"),
            CompileError::TooManyLocals => write!(f, "Too many local variables"),
            CompileError::Syntax(msg) => write!(f, "Syntax error: {}", msg),
            CompileError::RecurOutsideLoop => write!(f, "recur used outside loop/fn"),
        }
    }
}

impl std::error::Error for CompileError {}

/// Result type for compilation.
pub type Result<T> = std::result::Result<T, CompileError>;

/// Local variable during compilation.
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct Local {
    name: Symbol,
    depth: usize,
    is_captured: bool,
    is_mutable: bool,
}

/// Information about an upvalue (captured variable).
#[derive(Debug, Clone, Copy)]
struct Upvalue {
    /// Index in parent's locals (is_local=true) or parent's upvalues (is_local=false)
    index: u16,
    /// True if capturing from parent's locals, false if from parent's upvalues
    is_local: bool,
}

/// Loop context for compiling loop/recur.
#[derive(Debug, Clone)]
struct LoopContext {
    /// Jump target for recur.
    start_offset: usize,
    /// Stack offsets of loop bindings.
    binding_slots: Vec<u16>,
}

/// Enclosing scope information for closure compilation.
struct EnclosingScope<'a> {
    /// Parent's locals (for capturing) - reserved for future use
    #[allow(dead_code)]
    locals: &'a [Local],
    /// Parent's local name map
    local_map: &'a HashMap<Symbol, u16>,
    /// Parent's upvalues (for transitive capturing)
    upvalues: &'a [Upvalue],
}

/// Result of compiling a function, includes upvalue info for closure creation.
struct FunctionCompileResult {
    prototype: FunctionPrototype,
    upvalues: Vec<Upvalue>,
}

/// Compiler for function bodies.
///
/// This is a simpler compiler used for nested function compilation.
/// It doesn't need analysis results since we track locals directly.
struct FunctionCompiler<'a> {
    /// The chunk being built.
    chunk: Chunk,

    /// Function name.
    name: Option<Symbol>,

    /// Arity (number of required parameters).
    arity: u8,

    /// Whether this function has a rest parameter.
    has_rest: bool,

    /// Local variables in this function.
    locals: Vec<Local>,

    /// Current scope depth.
    scope_depth: usize,

    /// Map from symbol name to local slot.
    local_map: HashMap<Symbol, u16>,

    /// Upvalues captured by this function.
    upvalues: Vec<Upvalue>,

    /// Map from symbol name to upvalue index.
    upvalue_map: HashMap<Symbol, u16>,

    /// Enclosing scope (None for top-level functions).
    enclosing: Option<EnclosingScope<'a>>,

    /// Current loop context (for recur).
    loop_context: Option<LoopContext>,

    /// Current source location for debug info.
    current_line: LineInfo,
}

impl<'a> FunctionCompiler<'a> {
    fn new(
        name: Option<Symbol>,
        arity: u8,
        has_rest: bool,
        enclosing: Option<EnclosingScope<'a>>,
    ) -> Self {
        Self {
            chunk: Chunk::new(),
            name,
            arity,
            has_rest,
            locals: Vec::new(),
            scope_depth: 0,
            local_map: HashMap::new(),
            upvalues: Vec::new(),
            upvalue_map: HashMap::new(),
            enclosing,
            loop_context: None,
            current_line: LineInfo::default(),
        }
    }

    fn finish(self) -> FunctionCompileResult {
        let local_count = self.locals.len() as u16;
        let upvalue_count = self.upvalues.len() as u16;
        FunctionCompileResult {
            prototype: FunctionPrototype {
                name: self.name,
                arity: self.arity,
                has_rest: self.has_rest,
                chunk: self.chunk,
                upvalue_count,
                local_count,
            },
            upvalues: self.upvalues,
        }
    }

    fn emit(&mut self, op: OpCode) {
        self.chunk.emit(op, self.current_line);
    }

    fn emit_constant(&mut self, value: KlujurVal) -> Result<()> {
        let idx = self
            .chunk
            .add_constant(value)
            .ok_or(CompileError::TooManyConstants)?;
        self.emit(OpCode::Const(idx));
        Ok(())
    }

    fn add_constant(&mut self, value: KlujurVal) -> Result<u16> {
        self.chunk
            .add_constant(value)
            .ok_or(CompileError::TooManyConstants)
    }

    fn emit_jump(&mut self, op: OpCode) -> usize {
        let offset = self.chunk.current_offset();
        self.emit(op);
        offset
    }

    fn patch_jump(&mut self, offset: usize) {
        self.chunk.patch_jump(offset);
    }

    fn define_local(&mut self, name: Symbol) -> u16 {
        let slot = self.locals.len() as u16;
        self.local_map.insert(name.clone(), slot);
        self.locals.push(Local {
            name,
            depth: self.scope_depth,
            is_captured: false,
            is_mutable: false,
        });
        slot
    }

    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.scope_depth -= 1;
        while !self.locals.is_empty() && self.locals.last().unwrap().depth > self.scope_depth {
            let local = self.locals.pop().unwrap();
            self.local_map.remove(&local.name);
        }
    }

    fn compile_expr(&mut self, expr: &KlujurVal) -> Result<()> {
        match expr {
            KlujurVal::Nil => self.emit(OpCode::Nil),
            KlujurVal::Bool(true) => self.emit(OpCode::True),
            KlujurVal::Bool(false) => self.emit(OpCode::False),

            KlujurVal::Int(_)
            | KlujurVal::BigInt(_)
            | KlujurVal::Float(_)
            | KlujurVal::Ratio(..)
            | KlujurVal::BigRatio(..)
            | KlujurVal::Char(_)
            | KlujurVal::String(_)
            | KlujurVal::Keyword(_) => {
                self.emit_constant(expr.clone())?;
            }

            KlujurVal::Symbol(sym, _) => {
                self.compile_symbol(sym)?;
            }

            KlujurVal::List(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                self.compile_list(&items_vec)?;
            }

            KlujurVal::Vector(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                self.compile_vector(&items_vec)?;
            }

            KlujurVal::Map(map, _) => {
                self.emit_constant(KlujurVal::Map(map.clone(), None))?;
            }

            KlujurVal::Set(set, _) => {
                self.emit_constant(KlujurVal::Set(set.clone(), None))?;
            }

            _ => {
                self.emit_constant(expr.clone())?;
            }
        }
        Ok(())
    }

    fn compile_symbol(&mut self, sym: &Symbol) -> Result<()> {
        // 1. Check local variables
        if let Some(&slot) = self.local_map.get(sym) {
            self.emit(OpCode::LoadLocal(slot));
            return Ok(());
        }

        // 2. Check/add upvalue
        if let Some(upvalue_idx) = self.resolve_upvalue(sym) {
            self.emit(OpCode::LoadCapture(upvalue_idx));
            return Ok(());
        }

        // 3. Global lookup
        let idx = self.add_constant(KlujurVal::symbol(sym.clone()))?;
        self.emit(OpCode::LoadGlobal(idx));
        Ok(())
    }

    /// Try to resolve a symbol as an upvalue. Returns the upvalue index if found.
    fn resolve_upvalue(&mut self, sym: &Symbol) -> Option<u16> {
        // Already have this upvalue?
        if let Some(&idx) = self.upvalue_map.get(sym) {
            return Some(idx);
        }

        // Check enclosing scope
        let enclosing = self.enclosing.as_ref()?;

        // First, check if it's in the enclosing scope's locals
        if let Some(&local_slot) = enclosing.local_map.get(sym) {
            return Some(self.add_upvalue(sym.clone(), local_slot, true));
        }

        // Then, check if it's in the enclosing scope's upvalues
        // TODO: For transitive captures, we'd need to track names in upvalues
        // For now, we only support one level of capture
        let _ = enclosing.upvalues; // silence unused warning

        // For transitive upvalues, we'd need to track names in the enclosing upvalues
        // For now, just support one level of capture
        None
    }

    /// Add a new upvalue and return its index.
    fn add_upvalue(&mut self, name: Symbol, index: u16, is_local: bool) -> u16 {
        let upvalue_idx = self.upvalues.len() as u16;
        self.upvalues.push(Upvalue { index, is_local });
        self.upvalue_map.insert(name, upvalue_idx);
        upvalue_idx
    }

    fn compile_list(&mut self, items: &[KlujurVal]) -> Result<()> {
        if items.is_empty() {
            return self.emit_constant(KlujurVal::list(vec![]));
        }

        if let KlujurVal::Symbol(sym, _) = &items[0] {
            match sym.name() {
                "quote" => return self.compile_quote(&items[1..]),
                "if" => return self.compile_if(&items[1..]),
                "do" => return self.compile_do(&items[1..]),
                "let" | "let*" => return self.compile_let(&items[1..]),
                "fn" | "fn*" => return self.compile_fn(&items[1..]),
                "def" => return self.compile_def(&items[1..]),
                "set!" => return self.compile_set_bang(&items[1..]),
                "loop" => return self.compile_loop(&items[1..]),
                "recur" => return self.compile_recur(&items[1..]),
                _ => {}
            }
        }

        self.compile_call(items)
    }

    fn compile_quote(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
        } else {
            self.emit_constant(args[0].clone())?;
        }
        Ok(())
    }

    fn compile_if(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }
        self.compile_expr(&args[0])?;
        let else_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let end_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(else_jump);

        if args.len() > 2 {
            self.compile_expr(&args[2])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.patch_jump(end_jump);
        Ok(())
    }

    fn compile_do(&mut self, body: &[KlujurVal]) -> Result<()> {
        if body.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        for expr in &body[..body.len() - 1] {
            self.compile_expr(expr)?;
            self.emit(OpCode::Pop);
        }

        self.compile_expr(&body[body.len() - 1])
    }

    fn compile_let(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        self.begin_scope();

        let binding_count = if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            let mut count = 0;
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    self.compile_expr(chunk[1])?;
                    if let KlujurVal::Symbol(name, _) = chunk[0] {
                        self.define_local(name.clone());
                        count += 1;
                    }
                }
            }
            count
        } else {
            0
        };

        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        if binding_count > 0 {
            self.emit(OpCode::StoreLocal(
                self.locals.len() as u16 - binding_count as u16,
            ));
            for _ in 1..binding_count {
                self.emit(OpCode::Pop);
            }
        }

        self.end_scope();
        Ok(())
    }

    fn compile_fn(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        let (name, params, body_start) = if let KlujurVal::Symbol(n, _) = &args[0] {
            if args.len() < 2 {
                return Err(CompileError::Syntax("fn requires parameters".into()));
            }
            (Some(n.clone()), &args[1], 2)
        } else {
            (None, &args[0], 1)
        };

        let result = self.compile_nested_fn(name, params, &args[body_start..])?;
        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;
        self.emit(OpCode::Closure(idx));

        // Emit capture instructions for each upvalue
        for upvalue in &result.upvalues {
            if upvalue.is_local {
                self.emit(OpCode::CaptureLocal(upvalue.index));
            } else {
                self.emit(OpCode::CaptureUpvalue(upvalue.index));
            }
        }

        Ok(())
    }

    fn compile_nested_fn(
        &mut self,
        name: Option<Symbol>,
        params: &KlujurVal,
        body: &[KlujurVal],
    ) -> Result<FunctionCompileResult> {
        let mut param_names = Vec::new();
        let mut rest_param = None;
        let mut seen_rest = false;

        if let KlujurVal::Vector(param_vec, _) = params {
            for param in param_vec.iter() {
                match param {
                    KlujurVal::Symbol(s, _) if s.name() == "&" => {
                        seen_rest = true;
                    }
                    KlujurVal::Symbol(s, _) => {
                        if seen_rest {
                            rest_param = Some(s.clone());
                        } else {
                            param_names.push(s.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        let arity = param_names.len() as u8;
        let has_rest = rest_param.is_some();

        // Create enclosing scope from this compiler's state
        let enclosing = EnclosingScope {
            locals: &self.locals,
            local_map: &self.local_map,
            upvalues: &self.upvalues,
        };

        let mut fn_compiler = FunctionCompiler::new(name.clone(), arity, has_rest, Some(enclosing));

        if let Some(ref fn_name) = name {
            fn_compiler.define_local(fn_name.clone());
        }

        for param in &param_names {
            fn_compiler.define_local(param.clone());
        }

        if let Some(ref rest) = rest_param {
            fn_compiler.define_local(rest.clone());
        }

        if body.is_empty() {
            fn_compiler.emit(OpCode::Nil);
        } else {
            for expr in &body[..body.len() - 1] {
                fn_compiler.compile_expr(expr)?;
                fn_compiler.emit(OpCode::Pop);
            }
            fn_compiler.compile_expr(&body[body.len() - 1])?;
        }

        fn_compiler.emit(OpCode::Return);

        Ok(fn_compiler.finish())
    }

    fn compile_def(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("def requires a name".into()));
        }

        let name = match &args[0] {
            KlujurVal::Symbol(s, _) => s.clone(),
            _ => return Err(CompileError::Syntax("def name must be a symbol".into())),
        };

        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let idx = self.add_constant(KlujurVal::symbol(name))?;
        self.emit(OpCode::DefGlobal(idx));

        Ok(())
    }

    fn compile_set_bang(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.len() < 2 {
            return Err(CompileError::Syntax("set! requires name and value".into()));
        }

        let name = match &args[0] {
            KlujurVal::Symbol(s, _) => s,
            _ => return Err(CompileError::Syntax("set! target must be a symbol".into())),
        };

        self.compile_expr(&args[1])?;

        if let Some(&slot) = self.local_map.get(name) {
            self.emit(OpCode::Dup);
            self.emit(OpCode::StoreLocal(slot));
        } else {
            self.emit(OpCode::Dup);
            let idx = self.add_constant(KlujurVal::symbol(name.clone()))?;
            self.emit(OpCode::DefGlobal(idx));
        }

        Ok(())
    }

    fn compile_loop(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        self.begin_scope();

        let mut binding_slots = Vec::new();
        if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    self.compile_expr(chunk[1])?;
                    if let KlujurVal::Symbol(name, _) = chunk[0] {
                        let slot = self.define_local(name.clone());
                        binding_slots.push(slot);
                    }
                }
            }
        }

        let start_offset = self.chunk.current_offset();
        let old_loop = self.loop_context.take();
        self.loop_context = Some(LoopContext {
            start_offset,
            binding_slots: binding_slots.clone(),
        });

        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.loop_context = old_loop;

        let binding_count = binding_slots.len();
        if binding_count > 0 {
            self.emit(OpCode::StoreLocal(
                self.locals.len() as u16 - binding_count as u16,
            ));
            for _ in 1..binding_count {
                self.emit(OpCode::Pop);
            }
        }

        self.end_scope();

        Ok(())
    }

    fn compile_recur(&mut self, args: &[KlujurVal]) -> Result<()> {
        let ctx = self
            .loop_context
            .as_ref()
            .ok_or(CompileError::RecurOutsideLoop)?
            .clone();

        for arg in args {
            self.compile_expr(arg)?;
        }

        for &slot in ctx.binding_slots.iter().rev() {
            self.emit(OpCode::StoreLocal(slot));
        }

        let current = self.chunk.current_offset();
        let offset = ctx.start_offset as i16 - current as i16 - 1;
        self.emit(OpCode::Jump(offset));

        self.emit(OpCode::Nil);

        Ok(())
    }

    fn compile_call(&mut self, items: &[KlujurVal]) -> Result<()> {
        self.compile_expr(&items[0])?;

        let argc = items.len() - 1;
        if argc > 255 {
            return Err(CompileError::Syntax("Too many arguments".into()));
        }

        for arg in &items[1..] {
            self.compile_expr(arg)?;
        }

        self.emit(OpCode::Call(argc as u8));
        Ok(())
    }

    fn compile_vector(&mut self, items: &[KlujurVal]) -> Result<()> {
        let vec: Vec<_> = items.to_vec();
        self.emit_constant(KlujurVal::vector(vec))
    }
}

/// The bytecode compiler.
pub struct Compiler {
    /// The chunk being built.
    chunk: Chunk,

    /// Local variables in the current function.
    locals: Vec<Local>,

    /// Current scope depth (0 = function level).
    scope_depth: usize,

    /// Current loop context (for recur).
    loop_context: Option<LoopContext>,

    /// Analysis results (for variable resolution).
    #[allow(dead_code)]
    analysis: AnalysisResult,

    /// Map from symbol name to local slot.
    local_map: HashMap<Symbol, u16>,

    /// Current source location for debug info.
    current_line: LineInfo,
}

impl Compiler {
    /// Create a new compiler with analysis results.
    pub fn new(analysis: AnalysisResult) -> Self {
        Self {
            chunk: Chunk::new(),
            locals: Vec::new(),
            scope_depth: 0,
            loop_context: None,
            analysis,
            local_map: HashMap::new(),
            current_line: LineInfo::default(),
        }
    }

    /// Compile an expression and return the resulting chunk.
    pub fn compile(mut self, expr: &KlujurVal) -> Result<Chunk> {
        self.compile_expr(expr)?;
        self.emit(OpCode::Return);
        Ok(self.chunk)
    }

    /// Compile an expression.
    fn compile_expr(&mut self, expr: &KlujurVal) -> Result<()> {
        match expr {
            // Literals
            KlujurVal::Nil => self.emit(OpCode::Nil),
            KlujurVal::Bool(true) => self.emit(OpCode::True),
            KlujurVal::Bool(false) => self.emit(OpCode::False),

            KlujurVal::Int(_)
            | KlujurVal::BigInt(_)
            | KlujurVal::Float(_)
            | KlujurVal::Ratio(..)
            | KlujurVal::BigRatio(..)
            | KlujurVal::Char(_)
            | KlujurVal::String(_)
            | KlujurVal::Keyword(_) => {
                self.emit_constant(expr.clone())?;
            }

            // Symbol reference
            KlujurVal::Symbol(sym, _) => {
                self.compile_symbol(sym)?;
            }

            // List: special form or function call
            KlujurVal::List(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                self.compile_list(&items_vec)?;
            }

            // Vector literal
            KlujurVal::Vector(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                self.compile_vector(&items_vec)?;
            }

            // Map literal
            KlujurVal::Map(map, _) => {
                self.compile_map(map)?;
            }

            // Set literal
            KlujurVal::Set(set, _) => {
                self.compile_set(set)?;
            }

            // Other value types compile to constants
            _ => {
                self.emit_constant(expr.clone())?;
            }
        }
        Ok(())
    }

    fn compile_symbol(&mut self, sym: &Symbol) -> Result<()> {
        // Check if it's a local
        if let Some(&slot) = self.local_map.get(sym) {
            self.emit(OpCode::LoadLocal(slot));
            return Ok(());
        }

        // Otherwise it's a global
        let idx = self.add_constant(KlujurVal::symbol(sym.clone()))?;
        self.emit(OpCode::LoadGlobal(idx));
        Ok(())
    }

    fn compile_list(&mut self, items: &[KlujurVal]) -> Result<()> {
        if items.is_empty() {
            // Empty list is a constant
            return self.emit_constant(KlujurVal::list(vec![]));
        }

        // Check for special forms
        if let KlujurVal::Symbol(sym, _) = &items[0] {
            match sym.name() {
                "quote" => return self.compile_quote(&items[1..]),
                "if" => return self.compile_if(&items[1..]),
                "do" => return self.compile_do(&items[1..]),
                "let" | "let*" => return self.compile_let(&items[1..]),
                "fn" | "fn*" => return self.compile_fn(&items[1..]),
                "def" => return self.compile_def(&items[1..]),
                "set!" => return self.compile_set_bang(&items[1..]),
                "loop" => return self.compile_loop(&items[1..]),
                "recur" => return self.compile_recur(&items[1..]),
                _ => {}
            }
        }

        // Regular function call
        self.compile_call(items)
    }

    fn compile_quote(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
        } else {
            self.emit_constant(args[0].clone())?;
        }
        Ok(())
    }

    fn compile_if(&mut self, args: &[KlujurVal]) -> Result<()> {
        // Compile test
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }
        self.compile_expr(&args[0])?;

        // Jump to else if false
        let else_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Compile then branch
        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        // Jump over else
        let end_jump = self.emit_jump(OpCode::Jump(0));

        // Patch else jump
        self.patch_jump(else_jump);

        // Compile else branch
        if args.len() > 2 {
            self.compile_expr(&args[2])?;
        } else {
            self.emit(OpCode::Nil);
        }

        // Patch end jump
        self.patch_jump(end_jump);

        Ok(())
    }

    fn compile_do(&mut self, body: &[KlujurVal]) -> Result<()> {
        if body.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile all but last, discarding results
        for expr in &body[..body.len() - 1] {
            self.compile_expr(expr)?;
            self.emit(OpCode::Pop);
        }

        // Last expression is the result
        self.compile_expr(&body[body.len() - 1])
    }

    fn compile_let(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        self.begin_scope();

        // Parse bindings
        let binding_count = if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            let mut count = 0;
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    // Compile the value
                    self.compile_expr(chunk[1])?;

                    // Define the local
                    if let KlujurVal::Symbol(name, _) = &chunk[0] {
                        self.define_local(name.clone());
                        count += 1;
                    }
                }
            }
            count
        } else {
            0
        };

        // Compile body
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        // Clean up locals: swap result with bindings, then pop bindings
        // Result is on top, bindings below
        // We need to preserve the result and pop the bindings

        // For now, simple approach: store result in temp, pop bindings, push result
        // Actually, we can use a different approach:
        // After body evaluation, stack is: [bindings...] [result]
        // We need to get rid of bindings but keep result

        // Store result at binding[0] position, then pop extras
        if binding_count > 0 {
            // Move result down
            self.emit(OpCode::StoreLocal(
                self.locals.len() as u16 - binding_count as u16,
            ));
            // Pop the remaining binding slots (count - 1)
            for _ in 1..binding_count {
                self.emit(OpCode::Pop);
            }
        }

        self.end_scope();

        Ok(())
    }

    fn compile_fn(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        // Parse name and params
        let (name, params, body_start) = if let KlujurVal::Symbol(n, _) = &args[0] {
            // Named function
            if args.len() < 2 {
                return Err(CompileError::Syntax("fn requires parameters".into()));
            }
            (Some(n.clone()), &args[1], 2)
        } else {
            (None, &args[0], 1)
        };

        // Compile function body to a separate chunk
        let result = self.compile_function_body(name, params, &args[body_start..])?;
        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;

        // Emit closure instruction
        self.emit(OpCode::Closure(idx));

        // Emit capture instructions for each upvalue
        for upvalue in &result.upvalues {
            if upvalue.is_local {
                self.emit(OpCode::CaptureLocal(upvalue.index));
            } else {
                self.emit(OpCode::CaptureUpvalue(upvalue.index));
            }
        }

        Ok(())
    }

    fn compile_function_body(
        &mut self,
        name: Option<Symbol>,
        params: &KlujurVal,
        body: &[KlujurVal],
    ) -> Result<FunctionCompileResult> {
        // Parse parameters
        let mut param_names = Vec::new();
        let mut rest_param = None;
        let mut seen_rest = false;

        if let KlujurVal::Vector(param_vec, _) = params {
            for param in param_vec.iter() {
                match param {
                    KlujurVal::Symbol(s, _) if s.name() == "&" => {
                        seen_rest = true;
                    }
                    KlujurVal::Symbol(s, _) => {
                        if seen_rest {
                            rest_param = Some(s.clone());
                        } else {
                            param_names.push(s.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        let arity = param_names.len() as u8;
        let has_rest = rest_param.is_some();

        // Create enclosing scope from this compiler's state
        let enclosing = EnclosingScope {
            locals: &self.locals,
            local_map: &self.local_map,
            upvalues: &[], // Main compiler doesn't have upvalues
        };

        // Create a new compiler for the function body
        let mut fn_compiler = FunctionCompiler::new(name.clone(), arity, has_rest, Some(enclosing));

        // Define the function name as local slot 0 (for self-recursion)
        if let Some(ref fn_name) = name {
            fn_compiler.define_local(fn_name.clone());
        }

        // Define parameters as locals
        for param in &param_names {
            fn_compiler.define_local(param.clone());
        }

        // Define rest parameter if present
        if let Some(ref rest) = rest_param {
            fn_compiler.define_local(rest.clone());
        }

        // Compile the body
        if body.is_empty() {
            fn_compiler.emit(OpCode::Nil);
        } else {
            // Compile all but last expression, discarding results
            for expr in &body[..body.len() - 1] {
                fn_compiler.compile_expr(expr)?;
                fn_compiler.emit(OpCode::Pop);
            }
            // Last expression is the return value
            fn_compiler.compile_expr(&body[body.len() - 1])?;
        }

        // Emit return
        fn_compiler.emit(OpCode::Return);

        Ok(fn_compiler.finish())
    }

    fn compile_def(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("def requires a name".into()));
        }

        let name = match &args[0] {
            KlujurVal::Symbol(s, _) => s.clone(),
            _ => return Err(CompileError::Syntax("def name must be a symbol".into())),
        };

        // Compile the value (or nil if not provided)
        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        // Define in namespace
        let idx = self.add_constant(KlujurVal::symbol(name))?;
        self.emit(OpCode::DefGlobal(idx));

        Ok(())
    }

    fn compile_set_bang(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.len() < 2 {
            return Err(CompileError::Syntax("set! requires name and value".into()));
        }

        let name = match &args[0] {
            KlujurVal::Symbol(s, _) => s,
            _ => return Err(CompileError::Syntax("set! target must be a symbol".into())),
        };

        // Compile new value
        self.compile_expr(&args[1])?;

        // Store to local or global
        if let Some(&slot) = self.local_map.get(name) {
            self.emit(OpCode::Dup); // Keep value on stack as result
            self.emit(OpCode::StoreLocal(slot));
        } else {
            // Global set - for now just define it
            self.emit(OpCode::Dup);
            let idx = self.add_constant(KlujurVal::symbol(name.clone()))?;
            self.emit(OpCode::DefGlobal(idx));
        }

        Ok(())
    }

    fn compile_loop(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        self.begin_scope();

        // Parse bindings and record their slots
        let mut binding_slots = Vec::new();
        if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    self.compile_expr(chunk[1])?;
                    if let KlujurVal::Symbol(name, _) = &chunk[0] {
                        let slot = self.define_local(name.clone());
                        binding_slots.push(slot);
                    }
                }
            }
        }

        // Record loop start for recur
        let start_offset = self.chunk.current_offset();
        let old_loop = self.loop_context.take();
        self.loop_context = Some(LoopContext {
            start_offset,
            binding_slots: binding_slots.clone(),
        });

        // Compile body
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        // Restore old loop context
        self.loop_context = old_loop;

        // Clean up bindings (same as let)
        let binding_count = binding_slots.len();
        if binding_count > 0 {
            self.emit(OpCode::StoreLocal(
                self.locals.len() as u16 - binding_count as u16,
            ));
            for _ in 1..binding_count {
                self.emit(OpCode::Pop);
            }
        }

        self.end_scope();

        Ok(())
    }

    fn compile_recur(&mut self, args: &[KlujurVal]) -> Result<()> {
        let ctx = self
            .loop_context
            .as_ref()
            .ok_or(CompileError::RecurOutsideLoop)?
            .clone();

        // Compile new values
        for arg in args {
            self.compile_expr(arg)?;
        }

        // Store to binding slots in reverse order
        for &slot in ctx.binding_slots.iter().rev() {
            self.emit(OpCode::StoreLocal(slot));
        }

        // Jump back to loop start
        let current = self.chunk.current_offset();
        let offset = ctx.start_offset as i16 - current as i16 - 1;
        self.emit(OpCode::Jump(offset));

        // Recur doesn't return a value in normal flow
        // but we need something on the stack for type consistency
        self.emit(OpCode::Nil);

        Ok(())
    }

    fn compile_call(&mut self, items: &[KlujurVal]) -> Result<()> {
        // Compile function
        self.compile_expr(&items[0])?;

        // Compile arguments
        let argc = items.len() - 1;
        if argc > 255 {
            return Err(CompileError::Syntax("Too many arguments".into()));
        }

        for arg in &items[1..] {
            self.compile_expr(arg)?;
        }

        self.emit(OpCode::Call(argc as u8));
        Ok(())
    }

    fn compile_vector(&mut self, items: &[KlujurVal]) -> Result<()> {
        // For now, emit as a constant if all items are literals
        // Otherwise, we'd need a BUILD_VECTOR opcode
        let vec: Vec<_> = items.to_vec();
        self.emit_constant(KlujurVal::vector(vec))
    }

    fn compile_map(&mut self, map: &im::OrdMap<KlujurVal, KlujurVal>) -> Result<()> {
        self.emit_constant(KlujurVal::Map(map.clone(), None))
    }

    fn compile_set(&mut self, set: &im::OrdSet<KlujurVal>) -> Result<()> {
        self.emit_constant(KlujurVal::Set(set.clone(), None))
    }

    // =========================================================================
    // Helper methods
    // =========================================================================

    fn emit(&mut self, op: OpCode) {
        self.chunk.emit(op, self.current_line);
    }

    fn emit_constant(&mut self, value: KlujurVal) -> Result<()> {
        let idx = self.add_constant(value)?;
        self.emit(OpCode::Const(idx));
        Ok(())
    }

    fn add_constant(&mut self, value: KlujurVal) -> Result<u16> {
        self.chunk
            .add_constant(value)
            .ok_or(CompileError::TooManyConstants)
    }

    fn emit_jump(&mut self, op: OpCode) -> usize {
        let offset = self.chunk.current_offset();
        self.emit(op);
        offset
    }

    fn patch_jump(&mut self, offset: usize) {
        self.chunk.patch_jump(offset);
    }

    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.scope_depth -= 1;

        // Remove locals at this depth
        while !self.locals.is_empty() && self.locals.last().unwrap().depth > self.scope_depth {
            let local = self.locals.pop().unwrap();
            self.local_map.remove(&local.name);
        }
    }

    fn define_local(&mut self, name: Symbol) -> u16 {
        let slot = self.locals.len() as u16;
        self.local_map.insert(name.clone(), slot);
        self.locals.push(Local {
            name,
            depth: self.scope_depth,
            is_captured: false,
            is_mutable: false,
        });
        slot
    }
}

/// Wrapper to store FunctionPrototype in KlujurVal::Custom.
#[derive(Debug)]
pub struct FunctionPrototypeWrapper(pub FunctionPrototype);

impl CustomType for FunctionPrototypeWrapper {
    fn type_name(&self) -> &'static str {
        "FunctionPrototype"
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#<fn-proto {}>",
            self.0
                .name
                .as_ref()
                .map(|s| s.name())
                .unwrap_or("anonymous")
        )
    }
}
