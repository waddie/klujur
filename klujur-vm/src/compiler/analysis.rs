// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Semantic analysis pass: variable resolution, capture detection, mutation tracking.
//!
//! This pass walks the AST to:
//! 1. Build scope chains and resolve variable references
//! 2. Determine which variables are captured by closures
//! 3. Identify variables modified by `set!` (need heap allocation)
//! 4. Calculate stack offsets for locals

use std::collections::HashMap;

use klujur_parser::Symbol;
use klujur_parser::value::KlujurVal;

/// The kind of variable binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    /// Local variable on the stack in current frame.
    Local,
    /// Captured variable in closure's captures array (immutable).
    Capture,
    /// Captured variable in heap cell (mutable, shared).
    HeapCell,
    /// Global variable in namespace.
    Global,
}

/// Information about a resolved variable.
#[derive(Debug, Clone)]
pub struct VariableInfo {
    /// What kind of variable this is.
    pub kind: VarKind,

    /// Stack offset for locals (from frame base).
    pub stack_offset: Option<u16>,

    /// Index in closure's captures array.
    pub capture_index: Option<u16>,

    /// Index in heap cells (for mutable captures).
    pub heap_index: Option<u16>,

    /// Whether some inner closure captures this variable.
    pub is_captured: bool,

    /// Whether this variable is modified by `set!`.
    pub is_mutated: bool,
}

impl VariableInfo {
    /// Create info for a local variable.
    pub fn local(stack_offset: u16) -> Self {
        Self {
            kind: VarKind::Local,
            stack_offset: Some(stack_offset),
            capture_index: None,
            heap_index: None,
            is_captured: false,
            is_mutated: false,
        }
    }

    /// Create info for a global variable.
    pub fn global() -> Self {
        Self {
            kind: VarKind::Global,
            stack_offset: None,
            capture_index: None,
            heap_index: None,
            is_captured: false,
            is_mutated: false,
        }
    }
}

/// A scope in the scope chain.
#[derive(Debug)]
struct Scope {
    /// Variables defined in this scope.
    bindings: HashMap<Symbol, VariableInfo>,

    /// Parent scope (None for global scope).
    parent: Option<Box<Scope>>,

    /// Current stack offset for allocating locals.
    next_local: u16,

    /// Whether this is a function boundary (captures cross function boundaries).
    is_function: bool,
}

impl Scope {
    fn new(parent: Option<Box<Scope>>, is_function: bool) -> Self {
        let next_local = if is_function {
            0
        } else {
            parent.as_ref().map_or(0, |p| p.next_local)
        };

        Self {
            bindings: HashMap::new(),
            parent,
            next_local,
            is_function,
        }
    }

    fn define(&mut self, name: Symbol) -> u16 {
        let offset = self.next_local;
        self.bindings.insert(name, VariableInfo::local(offset));
        self.next_local += 1;
        offset
    }

    fn lookup(&self, name: &Symbol) -> Option<(VariableInfo, bool)> {
        if let Some(info) = self.bindings.get(name) {
            return Some((info.clone(), false));
        }

        if let Some(ref parent) = self.parent
            && let Some((mut info, crossed_function)) = parent.lookup(name)
        {
            let crossed = crossed_function || self.is_function;
            if crossed && info.kind == VarKind::Local {
                // Variable from outer function - needs to be captured
                info.is_captured = true;
            }
            return Some((info, crossed));
        }

        None
    }

    fn mark_mutated(&mut self, name: &Symbol) {
        if let Some(info) = self.bindings.get_mut(name) {
            info.is_mutated = true;
            return;
        }

        if let Some(ref mut parent) = self.parent {
            parent.mark_mutated(name);
        }
    }
}

/// Result of analysing an expression.
#[derive(Debug, Clone)]
pub struct AnalysisResult {
    /// Map from symbol occurrences to their resolved info.
    /// Key is the symbol, value is the resolution.
    pub resolutions: HashMap<usize, VariableInfo>,

    /// Variables captured by this function.
    pub captures: Vec<CaptureInfo>,

    /// Maximum stack depth needed.
    pub max_locals: u16,
}

/// Information about a captured variable.
#[derive(Debug, Clone)]
pub struct CaptureInfo {
    /// The symbol being captured.
    pub name: Symbol,

    /// Index in enclosing scope (local offset or capture index).
    pub source_index: u16,

    /// Whether capturing from immediate parent's locals (vs parent's captures).
    pub is_local: bool,

    /// Whether this variable is mutated (needs heap cell).
    pub is_mutable: bool,
}

/// The semantic analyser.
pub struct Analyser {
    /// Current scope chain.
    scope: Option<Box<Scope>>,

    /// Counter for creating unique resolution IDs.
    next_id: usize,

    /// Accumulated analysis results.
    resolutions: HashMap<usize, VariableInfo>,
}

impl Analyser {
    /// Create a new analyser.
    pub fn new() -> Self {
        Self {
            scope: Some(Box::new(Scope::new(None, true))),
            next_id: 0,
            resolutions: HashMap::new(),
        }
    }

    /// Analyse an expression and return the analysis result.
    pub fn analyse(&mut self, expr: &KlujurVal) -> AnalysisResult {
        self.analyse_expr(expr);

        AnalysisResult {
            resolutions: std::mem::take(&mut self.resolutions),
            captures: Vec::new(),
            max_locals: self.scope.as_ref().map_or(0, |s| s.next_local),
        }
    }

    fn analyse_expr(&mut self, expr: &KlujurVal) {
        match expr {
            KlujurVal::Symbol(sym, _) => {
                self.resolve_symbol(sym);
            }
            KlujurVal::List(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                self.analyse_list(&items_vec);
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    self.analyse_expr(item);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    self.analyse_expr(k);
                    self.analyse_expr(v);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    self.analyse_expr(item);
                }
            }
            // Literals don't need analysis
            _ => {}
        }
    }

    fn analyse_list(&mut self, items: &[KlujurVal]) {
        if items.is_empty() {
            return;
        }

        // Check for special forms
        if let KlujurVal::Symbol(sym, _) = &items[0] {
            match sym.name() {
                "quote" => return, // Don't analyse quoted forms
                "if" => return self.analyse_if(&items[1..]),
                "do" => return self.analyse_do(&items[1..]),
                "let" | "let*" => return self.analyse_let(&items[1..]),
                "fn" | "fn*" => return self.analyse_fn(&items[1..]),
                "def" => return self.analyse_def(&items[1..]),
                "set!" => return self.analyse_set(&items[1..]),
                "loop" => return self.analyse_loop(&items[1..]),
                "recur" => return self.analyse_recur(&items[1..]),
                _ => {}
            }
        }

        // Regular function call: analyse all subexpressions
        for item in items {
            self.analyse_expr(item);
        }
    }

    fn analyse_if(&mut self, args: &[KlujurVal]) {
        if !args.is_empty() {
            self.analyse_expr(&args[0]); // test
        }
        if args.len() > 1 {
            self.analyse_expr(&args[1]); // then
        }
        if args.len() > 2 {
            self.analyse_expr(&args[2]); // else
        }
    }

    fn analyse_do(&mut self, body: &[KlujurVal]) {
        for expr in body {
            self.analyse_expr(expr);
        }
    }

    fn analyse_let(&mut self, args: &[KlujurVal]) {
        if args.is_empty() {
            return;
        }

        // Enter new scope for let bindings
        self.push_scope(false);

        // Parse bindings vector
        if let KlujurVal::Vector(bindings, _) = &args[0] {
            let pairs: Vec<_> = bindings.iter().collect();
            for chunk in pairs.chunks(2) {
                if chunk.len() == 2 {
                    // Analyse the value first
                    self.analyse_expr(chunk[1]);

                    // Then define the binding
                    if let KlujurVal::Symbol(name, _) = &chunk[0] {
                        self.define_local(name.clone());
                    }
                }
            }
        }

        // Analyse body
        for expr in &args[1..] {
            self.analyse_expr(expr);
        }

        self.pop_scope();
    }

    fn analyse_fn(&mut self, args: &[KlujurVal]) {
        if args.is_empty() {
            return;
        }

        // Enter function scope
        self.push_scope(true);

        // Parse parameters
        let (params, body_start) = if let KlujurVal::Symbol(..) = &args[0] {
            // Named function: (fn name [params] body)
            if args.len() > 1 {
                if let KlujurVal::Symbol(name, _) = &args[0] {
                    self.define_local(name.clone());
                }
                (&args[1], 2)
            } else {
                return;
            }
        } else {
            // Anonymous: (fn [params] body)
            (&args[0], 1)
        };

        // Define parameters
        if let KlujurVal::Vector(param_vec, _) = params {
            for param in param_vec.iter() {
                match param {
                    KlujurVal::Symbol(name, _) if name.name() != "&" => {
                        self.define_local(name.clone());
                    }
                    _ => {}
                }
            }
        }

        // Analyse body
        for expr in &args[body_start..] {
            self.analyse_expr(expr);
        }

        self.pop_scope();
    }

    fn analyse_def(&mut self, args: &[KlujurVal]) {
        // def doesn't create a local, it defines a global
        if args.len() > 1 {
            self.analyse_expr(&args[1]);
        }
    }

    fn analyse_set(&mut self, args: &[KlujurVal]) {
        if args.is_empty() {
            return;
        }

        // Mark the variable as mutated
        if let KlujurVal::Symbol(name, _) = &args[0]
            && let Some(scope) = &mut self.scope
        {
            scope.mark_mutated(name);
        }

        // Analyse the new value
        if args.len() > 1 {
            self.analyse_expr(&args[1]);
        }
    }

    fn analyse_loop(&mut self, args: &[KlujurVal]) {
        // Loop is similar to let
        self.analyse_let(args);
    }

    fn analyse_recur(&mut self, args: &[KlujurVal]) {
        // Just analyse the arguments
        for arg in args {
            self.analyse_expr(arg);
        }
    }

    fn resolve_symbol(&mut self, sym: &Symbol) {
        let id = self.next_id;
        self.next_id += 1;

        let info = if let Some(scope) = &self.scope {
            if let Some((info, _crossed)) = scope.lookup(sym) {
                info
            } else {
                VariableInfo::global()
            }
        } else {
            VariableInfo::global()
        };

        self.resolutions.insert(id, info);
    }

    fn define_local(&mut self, name: Symbol) {
        if let Some(scope) = &mut self.scope {
            scope.define(name);
        }
    }

    fn push_scope(&mut self, is_function: bool) {
        let parent = self.scope.take();
        self.scope = Some(Box::new(Scope::new(parent, is_function)));
    }

    fn pop_scope(&mut self) {
        if let Some(scope) = self.scope.take() {
            self.scope = scope.parent;
        }
    }
}

impl Default for Analyser {
    fn default() -> Self {
        Self::new()
    }
}
