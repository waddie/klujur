// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Code generation: transforms analysed AST to bytecode.

use std::any::Any;
use std::collections::HashMap;
use std::rc::Rc;

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
    /// True if this captured variable is mutated via set!
    is_mutable: bool,
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
    #[allow(dead_code)]
    upvalues: &'a [Upvalue],
    /// Parent's upvalue name map (for transitive capturing)
    upvalue_names: &'a HashMap<Symbol, u16>,
    /// Parent's boxed locals (for mutable captures)
    boxed_locals: &'a std::collections::HashSet<Symbol>,
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

    /// Whether this is a multi-arity function (handles its own arity dispatch).
    is_multi_arity: bool,

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

    /// Set of variables that are targets of set! in this function.
    /// Used to determine which captures need heap cells.
    mutated_vars: std::collections::HashSet<Symbol>,

    /// Set of locals that need heap cells (are captured and mutated by nested functions).
    boxed_locals: std::collections::HashSet<Symbol>,
}

impl<'a> FunctionCompiler<'a> {
    #[allow(dead_code)]
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
            is_multi_arity: false,
            locals: Vec::new(),
            scope_depth: 0,
            local_map: HashMap::new(),
            upvalues: Vec::new(),
            upvalue_map: HashMap::new(),
            enclosing,
            loop_context: None,
            current_line: LineInfo::default(),
            mutated_vars: std::collections::HashSet::new(),
            boxed_locals: std::collections::HashSet::new(),
        }
    }

    fn new_multi_arity(
        name: Option<Symbol>,
        min_arity: u8,
        enclosing: Option<EnclosingScope<'a>>,
    ) -> Self {
        Self {
            chunk: Chunk::new(),
            name,
            arity: min_arity,
            has_rest: false,
            is_multi_arity: true,
            locals: Vec::new(),
            scope_depth: 0,
            local_map: HashMap::new(),
            upvalues: Vec::new(),
            upvalue_map: HashMap::new(),
            enclosing,
            loop_context: None,
            current_line: LineInfo::default(),
            mutated_vars: std::collections::HashSet::new(),
            boxed_locals: std::collections::HashSet::new(),
        }
    }

    fn with_mutated_vars(
        name: Option<Symbol>,
        arity: u8,
        has_rest: bool,
        enclosing: Option<EnclosingScope<'a>>,
        mutated_vars: std::collections::HashSet<Symbol>,
    ) -> Self {
        Self {
            chunk: Chunk::new(),
            name,
            arity,
            has_rest,
            is_multi_arity: false,
            locals: Vec::new(),
            scope_depth: 0,
            local_map: HashMap::new(),
            upvalues: Vec::new(),
            upvalue_map: HashMap::new(),
            enclosing,
            loop_context: None,
            current_line: LineInfo::default(),
            mutated_vars,
            boxed_locals: std::collections::HashSet::new(),
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
                is_multi_arity: self.is_multi_arity,
                chunk: Rc::new(self.chunk),
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
            // Check if this local is boxed (needs heap cell access)
            if self.boxed_locals.contains(sym) {
                self.emit(OpCode::LoadLocalHeap(slot));
            } else {
                self.emit(OpCode::LoadLocal(slot));
            }
            return Ok(());
        }

        // 2. Check/add upvalue
        if let Some((upvalue_idx, is_mutable)) = self.resolve_upvalue(sym) {
            if is_mutable {
                self.emit(OpCode::LoadHeap(upvalue_idx));
            } else {
                self.emit(OpCode::LoadCapture(upvalue_idx));
            }
            return Ok(());
        }

        // 3. Global lookup
        let idx = self.add_constant(KlujurVal::symbol(sym.clone()))?;
        self.emit(OpCode::LoadGlobal(idx));
        Ok(())
    }

    /// Try to resolve a symbol as an upvalue. Returns (upvalue_index, is_mutable) if found.
    fn resolve_upvalue(&mut self, sym: &Symbol) -> Option<(u16, bool)> {
        // Already have this upvalue?
        if let Some(&idx) = self.upvalue_map.get(sym) {
            let is_mutable = self
                .upvalues
                .get(idx as usize)
                .map(|uv| uv.is_mutable)
                .unwrap_or(false);
            return Some((idx, is_mutable));
        }

        // Check enclosing scope
        let enclosing = self.enclosing.as_ref()?;

        // Check if this variable is mutated in the current function
        let is_mutated_here = self.mutated_vars.contains(sym);

        // First, check if it's in the enclosing scope's locals
        if let Some(&local_slot) = enclosing.local_map.get(sym) {
            // Variable is mutable if either:
            // 1. It's boxed in the parent scope (another closure mutates it)
            // 2. This function mutates it
            let is_boxed_in_parent = enclosing.boxed_locals.contains(sym);
            let is_mutable = is_boxed_in_parent || is_mutated_here;
            let idx = self.add_upvalue(sym.clone(), local_slot, true, is_mutable);
            return Some((idx, is_mutable));
        }

        // Then, check if it's in the enclosing scope's upvalues (transitive capture)
        if let Some(&upvalue_idx) = enclosing.upvalue_names.get(sym) {
            // For transitive captures, check if parent's upvalue is mutable
            let parent_is_mutable = enclosing
                .upvalues
                .get(upvalue_idx as usize)
                .map(|uv| uv.is_mutable)
                .unwrap_or(false);
            // Mutable if either parent says it's mutable OR we mutate it here
            let is_mutable = parent_is_mutable || is_mutated_here;
            let idx = self.add_upvalue(sym.clone(), upvalue_idx, false, is_mutable);
            return Some((idx, is_mutable));
        }

        None
    }

    /// Add a new upvalue and return its index.
    fn add_upvalue(&mut self, name: Symbol, index: u16, is_local: bool, is_mutable: bool) -> u16 {
        let upvalue_idx = self.upvalues.len() as u16;
        self.upvalues.push(Upvalue {
            index,
            is_local,
            is_mutable,
        });
        self.upvalue_map.insert(name.clone(), upvalue_idx);
        // Track mutability info in upvalue_names for transitive captures
        upvalue_idx
    }

    /// Recursively collect all free variables in an expression.
    /// `bound` contains variables bound in outer scopes (params, let bindings).
    fn collect_free_vars(
        expr: &KlujurVal,
        bound: &std::collections::HashSet<Symbol>,
        free_vars: &mut Vec<Symbol>,
    ) {
        match expr {
            KlujurVal::Symbol(sym, _) => {
                if !bound.contains(sym) && !free_vars.contains(sym) {
                    free_vars.push(sym.clone());
                }
            }
            KlujurVal::List(items, _) => {
                if items.is_empty() {
                    return;
                }
                let items_vec: Vec<_> = items.iter().collect();

                // Check for special forms that introduce bindings
                if let KlujurVal::Symbol(sym, _) = &items_vec[0] {
                    match sym.name() {
                        "quote" => return, // Don't descend into quoted forms
                        "fn" | "fn*" => {
                            // fn introduces new binding scope
                            // Skip the name if present, parse params, scan body
                            let (params_idx, body_start) = if items_vec.len() > 1 {
                                if let KlujurVal::Symbol(_, _) = &items_vec[1] {
                                    (2, 3) // Named fn
                                } else {
                                    (1, 2) // Anonymous fn
                                }
                            } else {
                                return;
                            };

                            let mut fn_bound = bound.clone();

                            // Add fn name if present
                            if params_idx == 2
                                && let KlujurVal::Symbol(name, _) = &items_vec[1]
                            {
                                fn_bound.insert(name.clone());
                            }

                            // Add parameters to bound
                            if params_idx < items_vec.len()
                                && let KlujurVal::Vector(params, _) = &items_vec[params_idx]
                            {
                                for p in params.iter() {
                                    if let KlujurVal::Symbol(s, _) = p
                                        && s.name() != "&"
                                    {
                                        fn_bound.insert(s.clone());
                                    }
                                }
                            }

                            // Scan body
                            for item in items_vec.iter().skip(body_start) {
                                Self::collect_free_vars(item, &fn_bound, free_vars);
                            }
                            return;
                        }
                        "let" | "let*" => {
                            // let introduces bindings
                            let mut let_bound = bound.clone();
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        // Scan value expression first
                                        Self::collect_free_vars(chunk[1], &let_bound, free_vars);
                                        // Then add binding
                                        if let KlujurVal::Symbol(s, _) = chunk[0] {
                                            let_bound.insert(s.clone());
                                        }
                                    }
                                }
                            }
                            // Scan body
                            for item in items_vec.iter().skip(2) {
                                Self::collect_free_vars(item, &let_bound, free_vars);
                            }
                            return;
                        }
                        "loop" => {
                            // loop introduces bindings similar to let
                            let mut loop_bound = bound.clone();
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        Self::collect_free_vars(chunk[1], &loop_bound, free_vars);
                                        if let KlujurVal::Symbol(s, _) = chunk[0] {
                                            loop_bound.insert(s.clone());
                                        }
                                    }
                                }
                            }
                            for item in items_vec.iter().skip(2) {
                                Self::collect_free_vars(item, &loop_bound, free_vars);
                            }
                            return;
                        }
                        _ => {}
                    }
                }

                // Generic list: scan all elements
                for item in items_vec {
                    Self::collect_free_vars(item, bound, free_vars);
                }
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    Self::collect_free_vars(item, bound, free_vars);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    Self::collect_free_vars(k, bound, free_vars);
                    Self::collect_free_vars(v, bound, free_vars);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    Self::collect_free_vars(item, bound, free_vars);
                }
            }
            _ => {} // Literals, etc. - no free variables
        }
    }

    /// Recursively collect all set! targets in an expression.
    /// `bound` contains variables bound in the current scope (not used for filtering).
    /// `mutated` collects ALL variables that are targets of set!.
    fn collect_set_targets(
        expr: &KlujurVal,
        bound: &std::collections::HashSet<Symbol>,
        mutated: &mut std::collections::HashSet<Symbol>,
    ) {
        match expr {
            KlujurVal::List(items, _) => {
                if items.is_empty() {
                    return;
                }
                let items_vec: Vec<_> = items.iter().collect();

                // Check for set!
                if let KlujurVal::Symbol(sym, _) = &items_vec[0] {
                    if sym.name() == "set!" && items_vec.len() >= 2 {
                        // Found a set! - record the target (all targets, not just bound ones)
                        // This allows us to know which captures are mutated
                        if let KlujurVal::Symbol(target, _) = &items_vec[1] {
                            mutated.insert(target.clone());
                        }
                        // Also scan the value expression
                        if items_vec.len() > 2 {
                            Self::collect_set_targets(items_vec[2], bound, mutated);
                        }
                        return;
                    }

                    // Handle special forms that introduce bindings
                    match sym.name() {
                        "quote" => return,
                        "fn" | "fn*" => {
                            // fn introduces new binding scope - don't scan into nested fns
                            // (they have their own set of mutable captures)
                            return;
                        }
                        "let" | "let*" => {
                            let mut let_bound = bound.clone();
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        Self::collect_set_targets(chunk[1], &let_bound, mutated);
                                        if let KlujurVal::Symbol(s, _) = chunk[0] {
                                            let_bound.insert(s.clone());
                                        }
                                    }
                                }
                            }
                            for item in items_vec.iter().skip(2) {
                                Self::collect_set_targets(item, &let_bound, mutated);
                            }
                            return;
                        }
                        "loop" => {
                            let mut loop_bound = bound.clone();
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        Self::collect_set_targets(chunk[1], &loop_bound, mutated);
                                        if let KlujurVal::Symbol(s, _) = chunk[0] {
                                            loop_bound.insert(s.clone());
                                        }
                                    }
                                }
                            }
                            for item in items_vec.iter().skip(2) {
                                Self::collect_set_targets(item, &loop_bound, mutated);
                            }
                            return;
                        }
                        _ => {}
                    }
                }

                // Generic list: scan all elements
                for item in items_vec {
                    Self::collect_set_targets(item, bound, mutated);
                }
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    Self::collect_set_targets(item, bound, mutated);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    Self::collect_set_targets(k, bound, mutated);
                    Self::collect_set_targets(v, bound, mutated);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    Self::collect_set_targets(item, bound, mutated);
                }
            }
            _ => {}
        }
    }

    /// Find which of my locals are captured and mutated by nested functions.
    /// `my_locals` - the locals defined in the current scope (that could be boxed)
    /// Returns the set of my locals that need heap cells.
    fn collect_boxed_locals(
        exprs: &[KlujurVal],
        my_locals: &std::collections::HashSet<Symbol>,
    ) -> std::collections::HashSet<Symbol> {
        let mut boxed = std::collections::HashSet::new();
        for expr in exprs {
            Self::collect_boxed_locals_expr(expr, my_locals, &mut boxed);
        }
        boxed
    }

    /// Helper for collect_boxed_locals that recursively scans expressions.
    fn collect_boxed_locals_expr(
        expr: &KlujurVal,
        my_locals: &std::collections::HashSet<Symbol>,
        boxed: &mut std::collections::HashSet<Symbol>,
    ) {
        match expr {
            KlujurVal::List(items, _) => {
                if items.is_empty() {
                    return;
                }
                let items_vec: Vec<_> = items.iter().collect();

                if let KlujurVal::Symbol(sym, _) = &items_vec[0] {
                    match sym.name() {
                        "quote" => return,
                        "fn" | "fn*" => {
                            // Found a nested function - scan its body for set! targeting my_locals
                            // Parse the fn form to find the body
                            let (body_start, fn_params) = if items_vec.len() > 1 {
                                // Check for name or params
                                let mut idx = 1;
                                // Skip optional name
                                if let KlujurVal::Symbol(_, _) = &items_vec[idx] {
                                    idx += 1;
                                }
                                // Check for multi-arity
                                if idx < items_vec.len() {
                                    if let KlujurVal::List(_, _) = &items_vec[idx] {
                                        // Multi-arity - scan each arity form
                                        for arity_form in items_vec.iter().skip(idx) {
                                            if let KlujurVal::List(arity_items, _) = arity_form {
                                                let arity_vec: Vec<_> =
                                                    arity_items.iter().collect();
                                                if !arity_vec.is_empty() {
                                                    // Skip params, scan body
                                                    for body_item in arity_vec.iter().skip(1) {
                                                        Self::scan_nested_fn_for_set(
                                                            body_item, my_locals, boxed,
                                                        );
                                                    }
                                                }
                                            }
                                        }
                                        return;
                                    } else if let KlujurVal::Vector(params, _) = &items_vec[idx] {
                                        (idx + 1, Some(params))
                                    } else {
                                        return;
                                    }
                                } else {
                                    return;
                                }
                            } else {
                                return;
                            };
                            // Single arity - scan body
                            let _ = fn_params; // params define local scope, but we're looking for my_locals
                            for body_item in items_vec.iter().skip(body_start) {
                                Self::scan_nested_fn_for_set(body_item, my_locals, boxed);
                            }
                            return;
                        }
                        "let" | "let*" => {
                            // Scan binding values and body
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        Self::collect_boxed_locals_expr(chunk[1], my_locals, boxed);
                                    }
                                }
                            }
                            for item in items_vec.iter().skip(2) {
                                Self::collect_boxed_locals_expr(item, my_locals, boxed);
                            }
                            return;
                        }
                        "loop" => {
                            if items_vec.len() > 1
                                && let KlujurVal::Vector(bindings, _) = &items_vec[1]
                            {
                                let pairs: Vec<_> = bindings.iter().collect();
                                for chunk in pairs.chunks(2) {
                                    if chunk.len() == 2 {
                                        Self::collect_boxed_locals_expr(chunk[1], my_locals, boxed);
                                    }
                                }
                            }
                            for item in items_vec.iter().skip(2) {
                                Self::collect_boxed_locals_expr(item, my_locals, boxed);
                            }
                            return;
                        }
                        _ => {}
                    }
                }

                // Scan all items
                for item in items_vec {
                    Self::collect_boxed_locals_expr(item, my_locals, boxed);
                }
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    Self::collect_boxed_locals_expr(item, my_locals, boxed);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    Self::collect_boxed_locals_expr(k, my_locals, boxed);
                    Self::collect_boxed_locals_expr(v, my_locals, boxed);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    Self::collect_boxed_locals_expr(item, my_locals, boxed);
                }
            }
            _ => {}
        }
    }

    /// Scan a nested function for set! calls that target variables from an outer scope.
    fn scan_nested_fn_for_set(
        expr: &KlujurVal,
        outer_locals: &std::collections::HashSet<Symbol>,
        boxed: &mut std::collections::HashSet<Symbol>,
    ) {
        match expr {
            KlujurVal::List(items, _) => {
                if items.is_empty() {
                    return;
                }
                let items_vec: Vec<_> = items.iter().collect();

                if let KlujurVal::Symbol(sym, _) = &items_vec[0] {
                    match sym.name() {
                        "quote" => return,
                        "set!" => {
                            // Found set! - check if target is from outer scope
                            if items_vec.len() >= 2
                                && let KlujurVal::Symbol(target, _) = &items_vec[1]
                                && outer_locals.contains(target)
                            {
                                boxed.insert(target.clone());
                            }
                            // Also scan the value expression
                            if items_vec.len() > 2 {
                                Self::scan_nested_fn_for_set(items_vec[2], outer_locals, boxed);
                            }
                            return;
                        }
                        "fn" | "fn*" => {
                            // Nested fn inside nested fn - continue scanning
                            // (outer_locals are still from the outermost scope we care about)
                            let start = if items_vec.len() > 1 {
                                if let KlujurVal::Symbol(_, _) = &items_vec[1] {
                                    2
                                } else {
                                    1
                                }
                            } else {
                                return;
                            };
                            for item in items_vec.iter().skip(start) {
                                Self::scan_nested_fn_for_set(item, outer_locals, boxed);
                            }
                            return;
                        }
                        _ => {}
                    }
                }

                // Scan all items
                for item in items_vec {
                    Self::scan_nested_fn_for_set(item, outer_locals, boxed);
                }
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    Self::scan_nested_fn_for_set(item, outer_locals, boxed);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    Self::scan_nested_fn_for_set(k, outer_locals, boxed);
                    Self::scan_nested_fn_for_set(v, outer_locals, boxed);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    Self::scan_nested_fn_for_set(item, outer_locals, boxed);
                }
            }
            _ => {}
        }
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
                "when" => return self.compile_when(&items[1..]),
                "when-not" => return self.compile_when_not(&items[1..]),
                "and" => return self.compile_and(&items[1..]),
                "or" => return self.compile_or(&items[1..]),
                "if-not" => return self.compile_if_not(&items[1..]),
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

    /// (when test body...) - if test is truthy, evaluate body, else nil
    fn compile_when(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        let else_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Compile body (as do block)
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let end_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(else_jump);

        // Else branch is nil
        self.emit(OpCode::Nil);
        self.patch_jump(end_jump);
        Ok(())
    }

    /// (when-not test body...) - if test is falsy, evaluate body, else nil
    fn compile_when_not(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        // Jump to body if falsy (opposite of when)
        let then_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Test was truthy, so result is nil
        self.emit(OpCode::Nil);
        let end_jump = self.emit_jump(OpCode::Jump(0));

        // Test was falsy, compile body
        self.patch_jump(then_jump);
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.patch_jump(end_jump);
        Ok(())
    }

    /// (if-not test then else) - if test is falsy, then-branch, else else-branch
    fn compile_if_not(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        // Jump to "then" branch if falsy (opposite of if)
        let then_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Test was truthy - compile else branch (third arg or nil)
        if args.len() > 2 {
            self.compile_expr(&args[2])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let end_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(then_jump);

        // Test was falsy - compile then branch (second arg or nil)
        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.patch_jump(end_jump);
        Ok(())
    }

    /// (and ...) - short-circuit evaluation, returns last truthy or first falsy
    fn compile_and(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::True);
            return Ok(());
        }

        let mut end_jumps = Vec::new();

        for (i, arg) in args.iter().enumerate() {
            self.compile_expr(arg)?;

            if i < args.len() - 1 {
                // If falsy, jump to end with this value
                self.emit(OpCode::Dup);
                let jump = self.emit_jump(OpCode::PopJumpIfFalse(0));
                // If truthy, pop and continue to next
                self.emit(OpCode::Pop);
                end_jumps.push(jump);
            }
        }

        let after_all = self.chunk.code.len();
        for jump in end_jumps {
            self.patch_jump_to(jump, after_all);
        }

        Ok(())
    }

    /// (or ...) - short-circuit evaluation, returns first truthy or last falsy
    fn compile_or(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        let mut end_jumps = Vec::new();

        for (i, arg) in args.iter().enumerate() {
            self.compile_expr(arg)?;

            if i < args.len() - 1 {
                // If truthy, jump to end with this value
                self.emit(OpCode::Dup);
                // Use JumpIfTrue to keep the value and jump if truthy
                let jump = self.emit_jump(OpCode::JumpIfTrue(0));
                // If falsy, pop and continue to next
                self.emit(OpCode::Pop);
                end_jumps.push(jump);
            }
        }

        let after_all = self.chunk.code.len();
        for jump in end_jumps {
            self.patch_jump_to(jump, after_all);
        }

        Ok(())
    }

    /// Patch a jump instruction to jump to a specific target address.
    /// Calculates the relative offset from the jump instruction to the target.
    fn patch_jump_to(&mut self, jump_index: usize, target: usize) {
        let jump_distance = target as i16 - jump_index as i16 - 1;
        let op = &mut self.chunk.code[jump_index];
        match op {
            OpCode::Jump(offset) => *offset = jump_distance,
            OpCode::PopJumpIfFalse(offset) => *offset = jump_distance,
            OpCode::JumpIfTrue(offset) => *offset = jump_distance,
            _ => panic!("Not a jump instruction"),
        }
    }

    fn compile_let(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Pre-scan to find which locals need to be boxed
        // (are captured and mutated by nested functions)
        // We need to scan BOTH the binding values AND the body
        let mut let_locals = std::collections::HashSet::new();
        let mut all_exprs_to_scan = Vec::new();

        if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    if let KlujurVal::Symbol(name, _) = chunk[0] {
                        let_locals.insert(name.clone());
                    }
                    // Include binding value in scan
                    all_exprs_to_scan.push(chunk[1].clone());
                }
            }
        }
        // Include body in scan
        if args.len() > 1 {
            for expr in &args[1..] {
                all_exprs_to_scan.push(expr.clone());
            }
        }
        let new_boxed = Self::collect_boxed_locals(&all_exprs_to_scan, &let_locals);
        // Add new boxed locals to our tracking set
        for sym in &new_boxed {
            self.boxed_locals.insert(sym.clone());
        }

        self.begin_scope();

        let binding_count = if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            let mut count = 0;
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    self.compile_expr(chunk[1])?;
                    if let KlujurVal::Symbol(name, _) = chunk[0] {
                        let is_boxed = new_boxed.contains(name);
                        // If this local needs to be boxed, wrap it in a heap cell
                        if is_boxed {
                            self.emit(OpCode::Alloc);
                        }
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

        // Remove boxed locals that are going out of scope
        for sym in &new_boxed {
            self.boxed_locals.remove(sym);
        }

        Ok(())
    }

    fn compile_fn(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        // Check for multi-arity pattern: (fn name? ([x] ...) ([x y] ...) ...)
        // vs single-arity: (fn name? [x y] body...)
        let (name, arity_start) = if let KlujurVal::Symbol(n, _) = &args[0] {
            (Some(n.clone()), 1)
        } else {
            (None, 0)
        };

        // Check if all items from arity_start are lists (multi-arity pattern)
        let is_multi_arity = args.len() > arity_start
            && args[arity_start..]
                .iter()
                .all(|a| matches!(a, KlujurVal::List(..)));

        if is_multi_arity {
            // Multi-arity: (fn name? ([params1] body1...) ([params2] body2...) ...)
            return self.compile_multi_arity_fn(name, &args[arity_start..]);
        }

        // Single-arity: (fn name? [params] body...)
        if args.len() <= arity_start {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        let params = &args[arity_start];
        let body = &args[arity_start + 1..];

        let result = self.compile_nested_fn(name, params, body)?;
        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;
        self.emit(OpCode::Closure(idx));

        // Emit capture instructions for each upvalue
        for upvalue in &result.upvalues {
            if upvalue.is_mutable {
                // Mutable capture - use heap cell variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureHeapLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureHeapUpvalue(upvalue.index));
                }
            } else {
                // Immutable capture - use regular variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureUpvalue(upvalue.index));
                }
            }
        }

        Ok(())
    }

    /// Compile a multi-arity function: (fn name? ([x] body1) ([x y] body2) ...)
    fn compile_multi_arity_fn(
        &mut self,
        name: Option<Symbol>,
        arity_forms: &[KlujurVal],
    ) -> Result<()> {
        if arity_forms.is_empty() {
            return Err(CompileError::Syntax(
                "fn requires at least one arity".into(),
            ));
        }

        // Parse all arity forms
        let mut arities: Vec<(Vec<Symbol>, Option<Symbol>, Vec<&KlujurVal>)> = Vec::new();

        for form in arity_forms {
            if let KlujurVal::List(items, _) = form {
                if items.is_empty() {
                    return Err(CompileError::Syntax(
                        "arity form requires parameters".into(),
                    ));
                }
                let items_vec: Vec<_> = items.iter().collect();

                // First item should be params vector
                let params = items_vec[0];
                let body: Vec<&KlujurVal> = items_vec[1..].to_vec();

                let (param_names, rest_param) = self.parse_params(params)?;
                arities.push((param_names, rest_param, body));
            } else {
                return Err(CompileError::Syntax(
                    "multi-arity fn requires list forms".into(),
                ));
            }
        }

        // Sort by arity: fixed-arity first (by count), variadic last
        arities.sort_by(|a, b| {
            let a_variadic = a.1.is_some();
            let b_variadic = b.1.is_some();
            if a_variadic != b_variadic {
                a_variadic.cmp(&b_variadic) // Non-variadic before variadic
            } else {
                a.0.len().cmp(&b.0.len()) // Sort by param count
            }
        });

        // Pre-scan all bodies to collect free variables
        let mut all_bound: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        if let Some(ref n) = name {
            all_bound.insert(n.clone());
        }
        for (params, rest, _) in &arities {
            for p in params {
                all_bound.insert(p.clone());
            }
            if let Some(r) = rest {
                all_bound.insert(r.clone());
            }
        }

        let mut free_vars = Vec::new();
        for (params, rest, body) in &arities {
            let mut bound = all_bound.clone();
            for p in params {
                bound.insert(p.clone());
            }
            if let Some(r) = rest {
                bound.insert(r.clone());
            }
            for expr in body {
                Self::collect_free_vars(expr, &bound, &mut free_vars);
            }
        }

        // Ensure all free vars are captured in this scope
        for sym in &free_vars {
            if !self.local_map.contains_key(sym) && !self.upvalue_map.contains_key(sym) {
                let _ = self.resolve_upvalue(sym);
            }
        }

        // Now compile the multi-arity function into a single chunk with dispatch table
        let result = self.compile_multi_arity_body(name, &arities)?;

        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;
        self.emit(OpCode::Closure(idx));

        // Emit capture instructions
        for upvalue in &result.upvalues {
            if upvalue.is_mutable {
                // Mutable capture - use heap cell variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureHeapLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureHeapUpvalue(upvalue.index));
                }
            } else {
                // Immutable capture - use regular variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureUpvalue(upvalue.index));
                }
            }
        }

        Ok(())
    }

    /// Parse parameters from a vector, returning (fixed_params, rest_param)
    fn parse_params(&self, params: &KlujurVal) -> Result<(Vec<Symbol>, Option<Symbol>)> {
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
                    _ => {
                        return Err(CompileError::Syntax("fn parameters must be symbols".into()));
                    }
                }
            }
        } else {
            return Err(CompileError::Syntax(
                "fn parameters must be a vector".into(),
            ));
        }

        Ok((param_names, rest_param))
    }

    /// Compile a multi-arity function body with dispatch table
    fn compile_multi_arity_body(
        &mut self,
        name: Option<Symbol>,
        arities: &[(Vec<Symbol>, Option<Symbol>, Vec<&KlujurVal>)],
    ) -> Result<FunctionCompileResult> {
        // Create enclosing scope
        let empty_upvalue_map = HashMap::new();
        let enclosing = if self.enclosing.is_some() {
            EnclosingScope {
                locals: &self.locals,
                local_map: &self.local_map,
                upvalues: &self.upvalues,
                upvalue_names: &self.upvalue_map,
                boxed_locals: &self.boxed_locals,
            }
        } else {
            EnclosingScope {
                locals: &self.locals,
                local_map: &self.local_map,
                upvalues: &[],
                upvalue_names: &empty_upvalue_map,
                boxed_locals: &self.boxed_locals,
            }
        };

        // For multi-arity functions, store minimum arity for informational purposes.
        // The VM skips arity checking for multi-arity functions; ArityDispatch handles it.
        let min_arity = arities.iter().map(|(p, _, _)| p.len()).min().unwrap_or(0) as u8;

        // Create a new compiler for the multi-arity function
        // Use new_multi_arity() so VM skips arity check and rest handling
        let mut fn_compiler =
            FunctionCompiler::new_multi_arity(name.clone(), min_arity, Some(enclosing));

        // If named, reserve slot 0 for the function itself
        if let Some(ref fn_name) = name {
            fn_compiler.define_local(fn_name.clone());
        }

        // Emit the arity dispatch table at the start
        let entry_count = arities.len() as u8;
        fn_compiler.emit(OpCode::ArityDispatch(entry_count));

        // Reserve space for ArityEntry opcodes (we'll patch the offsets later)
        let mut entry_positions = Vec::new();
        for _ in 0..entry_count {
            entry_positions.push(fn_compiler.chunk.code.len());
            fn_compiler.emit(OpCode::ArityEntry {
                arity: 0,
                has_rest: false,
                offset: 0,
            });
        }

        // Compile each arity body and patch the dispatch table
        let mut body_positions = Vec::new();
        for (i, (params, rest, body)) in arities.iter().enumerate() {
            let body_start = fn_compiler.chunk.code.len();
            body_positions.push(body_start);

            // Start a new scope for this arity's parameters
            fn_compiler.begin_scope();

            // Define parameters as locals
            for param in params {
                fn_compiler.define_local(param.clone());
            }
            if let Some(rest_param) = rest {
                fn_compiler.define_local(rest_param.clone());
            }

            // Compile body
            if body.is_empty() {
                fn_compiler.emit(OpCode::Nil);
            } else {
                for expr in &body[..body.len() - 1] {
                    fn_compiler.compile_expr(expr)?;
                    fn_compiler.emit(OpCode::Pop);
                }
                fn_compiler.compile_expr(body[body.len() - 1])?;
            }

            fn_compiler.emit(OpCode::Return);
            fn_compiler.end_scope();

            // Patch the dispatch entry
            // Offset is relative to IP after reading ALL entries (position = 1 + entry_count)
            let ip_after_entries = 1 + entry_count as i32;
            let offset = (body_start as i32 - ip_after_entries) as i16;
            fn_compiler.chunk.code[entry_positions[i]] = OpCode::ArityEntry {
                arity: params.len() as u8,
                has_rest: rest.is_some(),
                offset,
            };
        }

        // Add error case at the end (unreachable if dispatch works correctly)
        // This is handled by ArityDispatch returning error

        Ok(fn_compiler.finish())
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

        // Pre-scan the nested function body to find all free variables.
        // This ensures transitive captures are set up in the parent first.
        let mut free_vars = Vec::new();
        let bound_vars: std::collections::HashSet<Symbol> = param_names
            .iter()
            .chain(rest_param.iter())
            .chain(name.iter())
            .cloned()
            .collect();
        for expr in body {
            Self::collect_free_vars(expr, &bound_vars, &mut free_vars);
        }

        // Pre-scan for set! targets to know which captures need heap cells
        let mut mutated_vars = std::collections::HashSet::new();
        for expr in body {
            Self::collect_set_targets(expr, &bound_vars, &mut mutated_vars);
        }

        // Ensure all free vars are resolvable in this scope (triggers upvalue capture if needed)
        for sym in &free_vars {
            // Check if it's already a local or upvalue in this compiler
            if self.local_map.contains_key(sym) || self.upvalue_map.contains_key(sym) {
                continue;
            }
            // Try to resolve as upvalue (this may add to our upvalue_map)
            let _ = self.resolve_upvalue(sym);
        }

        // Create enclosing scope from this compiler's state (now with any newly added upvalues)
        let enclosing = EnclosingScope {
            locals: &self.locals,
            local_map: &self.local_map,
            upvalues: &self.upvalues,
            upvalue_names: &self.upvalue_map,
            boxed_locals: &self.boxed_locals,
        };

        let mut fn_compiler = FunctionCompiler::with_mutated_vars(
            name.clone(),
            arity,
            has_rest,
            Some(enclosing),
            mutated_vars,
        );

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
            // Check if this local is boxed (needs heap cell access)
            if self.boxed_locals.contains(name) {
                self.emit(OpCode::StoreLocalHeap(slot));
            } else {
                self.emit(OpCode::StoreLocal(slot));
            }
        } else if let Some((upvalue_idx, is_mutable)) = self.resolve_upvalue(name) {
            // Setting a captured variable - must use heap cell
            if is_mutable {
                self.emit(OpCode::Dup);
                self.emit(OpCode::StoreHeap(upvalue_idx));
            } else {
                // This shouldn't happen if collect_set_targets worked correctly,
                // but fall back to treating as global for safety
                self.emit(OpCode::Dup);
                let idx = self.add_constant(KlujurVal::symbol(name.clone()))?;
                self.emit(OpCode::DefGlobal(idx));
            }
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
        // Check for specialized opcodes for known builtins
        if let KlujurVal::Symbol(sym, _) = &items[0]
            && (sym.namespace().is_none() || sym.namespace() == Some("klujur.core"))
            && let Some(()) = self.try_emit_builtin_opcode(sym.name(), &items[1..])?
        {
            return Ok(());
        }

        // Generic function call
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

    /// Try to emit a specialized opcode for a known builtin.
    /// Returns Ok(Some(())) if a specialized opcode was emitted, Ok(None) if not.
    fn try_emit_builtin_opcode(&mut self, name: &str, args: &[KlujurVal]) -> Result<Option<()>> {
        match (name, args.len()) {
            // Existing opcodes - sequence operations
            ("first", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::First);
                Ok(Some(()))
            }
            ("rest", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Rest);
                Ok(Some(()))
            }
            ("cons", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Cons);
                Ok(Some(()))
            }
            ("not", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Not);
                Ok(Some(()))
            }

            // New opcodes - collection operations
            ("get", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Get);
                Ok(Some(()))
            }
            ("get", 3) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.compile_expr(&args[2])?;
                self.emit(OpCode::GetDefault);
                Ok(Some(()))
            }
            ("assoc", 3) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.compile_expr(&args[2])?;
                self.emit(OpCode::Assoc);
                Ok(Some(()))
            }
            ("conj", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Conj);
                Ok(Some(()))
            }
            ("count", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Count);
                Ok(Some(()))
            }
            ("next", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Next);
                Ok(Some(()))
            }
            ("nth", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Nth);
                Ok(Some(()))
            }

            // Predicates
            ("nil?", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::NilP);
                Ok(Some(()))
            }
            ("empty?", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::EmptyP);
                Ok(Some(()))
            }

            // Arithmetic
            ("inc", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Inc);
                Ok(Some(()))
            }
            ("dec", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Dec);
                Ok(Some(()))
            }

            // Binary arithmetic (2-arity only)
            ("+", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Add);
                Ok(Some(()))
            }
            ("-", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Sub);
                Ok(Some(()))
            }
            ("*", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Mul);
                Ok(Some(()))
            }
            ("/", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Div);
                Ok(Some(()))
            }

            // Comparison (2-arity only)
            ("=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Eq);
                Ok(Some(()))
            }
            ("<", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Lt);
                Ok(Some(()))
            }
            (">", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Gt);
                Ok(Some(()))
            }
            ("<=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Le);
                Ok(Some(()))
            }
            (">=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Ge);
                Ok(Some(()))
            }

            // Not a specialized opcode
            _ => Ok(None),
        }
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

    /// Set of locals that need heap cells (are captured and mutated by nested functions).
    boxed_locals: std::collections::HashSet<Symbol>,
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
            boxed_locals: std::collections::HashSet::new(),
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
            // Check if this local is boxed (needs heap cell access)
            if self.boxed_locals.contains(sym) {
                self.emit(OpCode::LoadLocalHeap(slot));
            } else {
                self.emit(OpCode::LoadLocal(slot));
            }
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
                "when" => return self.compile_when(&items[1..]),
                "when-not" => return self.compile_when_not(&items[1..]),
                "and" => return self.compile_and(&items[1..]),
                "or" => return self.compile_or(&items[1..]),
                "if-not" => return self.compile_if_not(&items[1..]),
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

    /// (when test body...) - if test is truthy, evaluate body, else nil
    fn compile_when(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        let else_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Compile body (as do block)
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let end_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(else_jump);

        // Else branch is nil
        self.emit(OpCode::Nil);
        self.patch_jump(end_jump);
        Ok(())
    }

    /// (when-not test body...) - if test is falsy, evaluate body, else nil
    fn compile_when_not(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        // Jump to body if falsy (opposite of when)
        let then_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Test was truthy, so result is nil
        self.emit(OpCode::Nil);
        let end_jump = self.emit_jump(OpCode::Jump(0));

        // Test was falsy, compile body
        self.patch_jump(then_jump);
        if args.len() > 1 {
            self.compile_do(&args[1..])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.patch_jump(end_jump);
        Ok(())
    }

    /// (if-not test then else) - if test is falsy, then-branch, else else-branch
    fn compile_if_not(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Compile test
        self.compile_expr(&args[0])?;
        // Jump to "then" branch if falsy (opposite of if)
        let then_jump = self.emit_jump(OpCode::PopJumpIfFalse(0));

        // Test was truthy - compile else branch (third arg or nil)
        if args.len() > 2 {
            self.compile_expr(&args[2])?;
        } else {
            self.emit(OpCode::Nil);
        }

        let end_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(then_jump);

        // Test was falsy - compile then branch (second arg or nil)
        if args.len() > 1 {
            self.compile_expr(&args[1])?;
        } else {
            self.emit(OpCode::Nil);
        }

        self.patch_jump(end_jump);
        Ok(())
    }

    /// (and ...) - short-circuit evaluation, returns last truthy or first falsy
    fn compile_and(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::True);
            return Ok(());
        }

        let mut end_jumps = Vec::new();

        for (i, arg) in args.iter().enumerate() {
            self.compile_expr(arg)?;

            if i < args.len() - 1 {
                // If falsy, jump to end with this value
                self.emit(OpCode::Dup);
                let jump = self.emit_jump(OpCode::PopJumpIfFalse(0));
                // If truthy, pop and continue to next
                self.emit(OpCode::Pop);
                end_jumps.push(jump);
            }
        }

        let after_all = self.chunk.code.len();
        for jump in end_jumps {
            self.patch_jump_to(jump, after_all);
        }

        Ok(())
    }

    /// (or ...) - short-circuit evaluation, returns first truthy or last falsy
    fn compile_or(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        let mut end_jumps = Vec::new();

        for (i, arg) in args.iter().enumerate() {
            self.compile_expr(arg)?;

            if i < args.len() - 1 {
                // If truthy, jump to end with this value
                self.emit(OpCode::Dup);
                // Use JumpIfTrue to keep the value and jump if truthy
                let jump = self.emit_jump(OpCode::JumpIfTrue(0));
                // If falsy, pop and continue to next
                self.emit(OpCode::Pop);
                end_jumps.push(jump);
            }
        }

        let after_all = self.chunk.code.len();
        for jump in end_jumps {
            self.patch_jump_to(jump, after_all);
        }

        Ok(())
    }

    /// Patch a jump instruction to jump to a specific target address.
    /// Calculates the relative offset from the jump instruction to the target.
    fn patch_jump_to(&mut self, jump_index: usize, target: usize) {
        let jump_distance = target as i16 - jump_index as i16 - 1;
        let op = &mut self.chunk.code[jump_index];
        match op {
            OpCode::Jump(offset) => *offset = jump_distance,
            OpCode::PopJumpIfFalse(offset) => *offset = jump_distance,
            OpCode::JumpIfTrue(offset) => *offset = jump_distance,
            _ => panic!("Not a jump instruction"),
        }
    }

    fn compile_let(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            self.emit(OpCode::Nil);
            return Ok(());
        }

        // Pre-scan to find which locals need to be boxed
        // (are captured and mutated by nested functions)
        // We need to scan BOTH the binding values AND the body
        let mut let_locals = std::collections::HashSet::new();
        let mut all_exprs_to_scan = Vec::new();

        if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    if let KlujurVal::Symbol(name, _) = chunk[0] {
                        let_locals.insert(name.clone());
                    }
                    // Include binding value in scan
                    all_exprs_to_scan.push(chunk[1].clone());
                }
            }
        }
        // Include body in scan
        if args.len() > 1 {
            for expr in &args[1..] {
                all_exprs_to_scan.push(expr.clone());
            }
        }
        let new_boxed = FunctionCompiler::collect_boxed_locals(&all_exprs_to_scan, &let_locals);
        // Add new boxed locals to our tracking set
        for sym in &new_boxed {
            self.boxed_locals.insert(sym.clone());
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
                        let is_boxed = new_boxed.contains(name);
                        // If this local needs to be boxed, wrap it in a heap cell
                        if is_boxed {
                            self.emit(OpCode::Alloc);
                        }
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

        // Remove boxed locals that are going out of scope
        for sym in &new_boxed {
            self.boxed_locals.remove(sym);
        }

        Ok(())
    }

    fn compile_fn(&mut self, args: &[KlujurVal]) -> Result<()> {
        if args.is_empty() {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        // Check for optional name
        let (name, arity_start) = if let KlujurVal::Symbol(n, _) = &args[0] {
            (Some(n.clone()), 1)
        } else {
            (None, 0)
        };

        // Detect multi-arity: (fn name? ([params1] body1...) ([params2] body2...) ...)
        let is_multi_arity = args.len() > arity_start
            && args[arity_start..]
                .iter()
                .all(|a| matches!(a, KlujurVal::List(..)));

        if is_multi_arity {
            // Multi-arity: compile via FunctionCompiler which has full support
            return self.compile_multi_arity_fn(name, &args[arity_start..]);
        }

        // Single-arity: (fn name? [params] body...)
        if args.len() <= arity_start {
            return Err(CompileError::Syntax("fn requires parameters".into()));
        }

        let params = &args[arity_start];
        let body_start = arity_start + 1;

        // Compile function body to a separate chunk
        let result = self.compile_function_body(name, params, &args[body_start..])?;
        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;

        // Emit closure instruction
        self.emit(OpCode::Closure(idx));

        // Emit capture instructions for each upvalue
        for upvalue in &result.upvalues {
            if upvalue.is_mutable {
                // Mutable capture - use heap cell variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureHeapLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureHeapUpvalue(upvalue.index));
                }
            } else {
                // Immutable capture - use regular variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureUpvalue(upvalue.index));
                }
            }
        }

        Ok(())
    }

    /// Compile a multi-arity function: (fn name? ([x] body1) ([x y] body2) ...)
    fn compile_multi_arity_fn(
        &mut self,
        name: Option<Symbol>,
        arity_forms: &[KlujurVal],
    ) -> Result<()> {
        if arity_forms.is_empty() {
            return Err(CompileError::Syntax(
                "fn requires at least one arity".into(),
            ));
        }

        // Parse each arity form
        let mut arities: Vec<(Vec<Symbol>, Option<Symbol>, Vec<&KlujurVal>)> = Vec::new();

        for form in arity_forms {
            if let KlujurVal::List(items, _) = form {
                if items.is_empty() {
                    return Err(CompileError::Syntax(
                        "arity form requires parameters".into(),
                    ));
                }
                let items_vec: Vec<_> = items.iter().collect();
                let (params, rest, body) = Self::parse_arity_params(&items_vec)?;
                arities.push((params, rest, body));
            } else {
                return Err(CompileError::Syntax("expected arity form (list)".into()));
            }
        }

        // Sort arities by param count (descending) for proper dispatch
        arities.sort_by(|a, b| b.0.len().cmp(&a.0.len()));

        // Compile the multi-arity function using FunctionCompiler
        let result = self.compile_multi_arity_body(name, &arities)?;
        let proto_val = KlujurVal::custom(FunctionPrototypeWrapper(result.prototype));
        let idx = self.add_constant(proto_val)?;

        self.emit(OpCode::Closure(idx));

        // Emit capture instructions for each upvalue
        for upvalue in &result.upvalues {
            if upvalue.is_mutable {
                // Mutable capture - use heap cell variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureHeapLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureHeapUpvalue(upvalue.index));
                }
            } else {
                // Immutable capture - use regular variants
                if upvalue.is_local {
                    self.emit(OpCode::CaptureLocal(upvalue.index));
                } else {
                    self.emit(OpCode::CaptureUpvalue(upvalue.index));
                }
            }
        }

        Ok(())
    }

    /// Parse parameters from an arity form
    fn parse_arity_params<'b>(
        items: &[&'b KlujurVal],
    ) -> Result<(Vec<Symbol>, Option<Symbol>, Vec<&'b KlujurVal>)> {
        if items.is_empty() {
            return Err(CompileError::Syntax(
                "arity form requires parameters".into(),
            ));
        }

        let mut param_names = Vec::new();
        let mut rest_param = None;
        let mut seen_rest = false;

        if let KlujurVal::Vector(params, _) = items[0] {
            for param in params.iter() {
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
        } else {
            return Err(CompileError::Syntax("expected parameters vector".into()));
        }

        let body = items[1..].to_vec();
        Ok((param_names, rest_param, body))
    }

    /// Compile a multi-arity function body with dispatch table
    fn compile_multi_arity_body(
        &mut self,
        name: Option<Symbol>,
        arities: &[(Vec<Symbol>, Option<Symbol>, Vec<&KlujurVal>)],
    ) -> Result<FunctionCompileResult> {
        // Create enclosing scope from this compiler's state
        let empty_upvalue_map = HashMap::new();
        let enclosing = EnclosingScope {
            locals: &self.locals,
            local_map: &self.local_map,
            upvalues: &[],
            upvalue_names: &empty_upvalue_map,
            boxed_locals: &self.boxed_locals,
        };

        // For multi-arity functions, store minimum arity for informational purposes.
        // The VM skips arity checking for multi-arity functions; ArityDispatch handles it.
        let min_arity = arities.iter().map(|(p, _, _)| p.len()).min().unwrap_or(0) as u8;

        // Create a new compiler for the multi-arity function
        // Use new_multi_arity() so VM skips arity check and rest handling
        let mut fn_compiler =
            FunctionCompiler::new_multi_arity(name.clone(), min_arity, Some(enclosing));

        // If named, reserve slot 0 for the function itself
        if let Some(ref fn_name) = name {
            fn_compiler.define_local(fn_name.clone());
        }

        // Emit the arity dispatch table at the start
        let entry_count = arities.len() as u8;
        fn_compiler.emit(OpCode::ArityDispatch(entry_count));

        // Reserve space for ArityEntry opcodes (we'll patch the offsets later)
        let mut entry_positions = Vec::new();
        for _ in 0..entry_count {
            entry_positions.push(fn_compiler.chunk.code.len());
            fn_compiler.emit(OpCode::ArityEntry {
                arity: 0,
                has_rest: false,
                offset: 0,
            });
        }

        // Compile each arity body and patch the dispatch table
        for (i, (params, rest, body)) in arities.iter().enumerate() {
            let body_start = fn_compiler.chunk.code.len();

            // Start a new scope for this arity's parameters
            fn_compiler.begin_scope();

            // Define parameters as locals
            for param in params {
                fn_compiler.define_local(param.clone());
            }
            if let Some(rest_param) = rest {
                fn_compiler.define_local(rest_param.clone());
            }

            // Compile body
            if body.is_empty() {
                fn_compiler.emit(OpCode::Nil);
            } else {
                for expr in &body[..body.len() - 1] {
                    fn_compiler.compile_expr(expr)?;
                    fn_compiler.emit(OpCode::Pop);
                }
                fn_compiler.compile_expr(body[body.len() - 1])?;
            }

            fn_compiler.emit(OpCode::Return);
            fn_compiler.end_scope();

            // Patch the dispatch entry
            // Offset is relative to IP after reading ALL entries (position = 1 + entry_count)
            let ip_after_entries = 1 + entry_count as i32;
            let offset = (body_start as i32 - ip_after_entries) as i16;
            fn_compiler.chunk.code[entry_positions[i]] = OpCode::ArityEntry {
                arity: params.len() as u8,
                has_rest: rest.is_some(),
                offset,
            };
        }

        Ok(fn_compiler.finish())
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

        // Pre-scan for set! targets to know which captures need heap cells
        let bound_vars: std::collections::HashSet<Symbol> = param_names
            .iter()
            .chain(rest_param.iter())
            .chain(name.iter())
            .cloned()
            .collect();
        let mut mutated_vars = std::collections::HashSet::new();
        for expr in body {
            FunctionCompiler::collect_set_targets(expr, &bound_vars, &mut mutated_vars);
        }

        // Create enclosing scope from this compiler's state
        // Main compiler doesn't have upvalues (it's the top-level)
        let empty_upvalue_map = HashMap::new();
        let enclosing = EnclosingScope {
            locals: &self.locals,
            local_map: &self.local_map,
            upvalues: &[],
            upvalue_names: &empty_upvalue_map,
            boxed_locals: &self.boxed_locals,
        };

        // Create a new compiler for the function body
        let mut fn_compiler = FunctionCompiler::with_mutated_vars(
            name.clone(),
            arity,
            has_rest,
            Some(enclosing),
            mutated_vars,
        );

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
            // Check if this local is boxed (needs heap cell access)
            if self.boxed_locals.contains(name) {
                self.emit(OpCode::StoreLocalHeap(slot));
            } else {
                self.emit(OpCode::StoreLocal(slot));
            }
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
        // Check for specialized opcodes for known builtins
        if let KlujurVal::Symbol(sym, _) = &items[0]
            && (sym.namespace().is_none() || sym.namespace() == Some("klujur.core"))
            && let Some(()) = self.try_emit_builtin_opcode(sym.name(), &items[1..])?
        {
            return Ok(());
        }

        // Generic function call
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

    /// Try to emit a specialized opcode for a known builtin.
    /// Returns Ok(Some(())) if a specialized opcode was emitted, Ok(None) if not.
    fn try_emit_builtin_opcode(&mut self, name: &str, args: &[KlujurVal]) -> Result<Option<()>> {
        match (name, args.len()) {
            // Existing opcodes - sequence operations
            ("first", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::First);
                Ok(Some(()))
            }
            ("rest", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Rest);
                Ok(Some(()))
            }
            ("cons", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Cons);
                Ok(Some(()))
            }
            ("not", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Not);
                Ok(Some(()))
            }

            // New opcodes - collection operations
            ("get", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Get);
                Ok(Some(()))
            }
            ("get", 3) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.compile_expr(&args[2])?;
                self.emit(OpCode::GetDefault);
                Ok(Some(()))
            }
            ("assoc", 3) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.compile_expr(&args[2])?;
                self.emit(OpCode::Assoc);
                Ok(Some(()))
            }
            ("conj", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Conj);
                Ok(Some(()))
            }
            ("count", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Count);
                Ok(Some(()))
            }
            ("next", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Next);
                Ok(Some(()))
            }
            ("nth", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Nth);
                Ok(Some(()))
            }

            // Predicates
            ("nil?", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::NilP);
                Ok(Some(()))
            }
            ("empty?", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::EmptyP);
                Ok(Some(()))
            }

            // Arithmetic
            ("inc", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Inc);
                Ok(Some(()))
            }
            ("dec", 1) => {
                self.compile_expr(&args[0])?;
                self.emit(OpCode::Dec);
                Ok(Some(()))
            }

            // Binary arithmetic (2-arity only)
            ("+", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Add);
                Ok(Some(()))
            }
            ("-", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Sub);
                Ok(Some(()))
            }
            ("*", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Mul);
                Ok(Some(()))
            }
            ("/", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Div);
                Ok(Some(()))
            }

            // Comparison (2-arity only)
            ("=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Eq);
                Ok(Some(()))
            }
            ("<", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Lt);
                Ok(Some(()))
            }
            (">", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Gt);
                Ok(Some(()))
            }
            ("<=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Le);
                Ok(Some(()))
            }
            (">=", 2) => {
                self.compile_expr(&args[0])?;
                self.compile_expr(&args[1])?;
                self.emit(OpCode::Ge);
                Ok(Some(()))
            }

            // Not a specialized opcode
            _ => Ok(None),
        }
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
