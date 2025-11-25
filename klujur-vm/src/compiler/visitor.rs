// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! AST visitor trait and implementations for expression analysis.
//!
//! This module provides a generic visitor pattern for traversing Klujur AST expressions,
//! with specialised visitors for collecting free variables, set! targets, and boxed locals.

use std::collections::HashSet;

use klujur_parser::symbol::Symbol;
use klujur_parser::value::KlujurVal;

/// Trait for visiting expressions in the AST.
///
/// Implement this trait to create custom visitors that walk the expression tree.
/// The default implementations traverse into child expressions.
pub trait ExprVisitor {
    /// Visit a symbol (identifier).
    fn visit_symbol(&mut self, _sym: &Symbol) {}

    /// Visit a list form. `head` is the symbol at the head of the list if present.
    fn visit_list(&mut self, _items: &[&KlujurVal], _head: Option<&str>) {}

    /// Visit a vector literal.
    fn visit_vector(&mut self, _items: &im::Vector<KlujurVal>) {}

    /// Visit a map literal.
    fn visit_map(&mut self, _map: &im::OrdMap<KlujurVal, KlujurVal>) {}

    /// Visit a set literal.
    fn visit_set(&mut self, _set: &im::OrdSet<KlujurVal>) {}

    /// Called before descending into a special form.
    /// Return false to skip descending (e.g., for `quote`).
    fn should_descend(&self, _form: &str) -> bool {
        true
    }

    /// Called when entering a new binding scope (fn, let, loop).
    /// Return the set of newly bound symbols.
    fn enter_scope(&mut self, _bindings: &[Symbol]) {}

    /// Called when exiting a binding scope.
    fn exit_scope(&mut self, _bindings: &[Symbol]) {}
}

/// Walk an expression tree, calling visitor methods at each node.
pub fn walk_expr<V: ExprVisitor>(expr: &KlujurVal, visitor: &mut V) {
    walk_expr_with_scope(expr, visitor, &HashSet::new());
}

/// Walk an expression tree with a set of bound variables.
pub fn walk_expr_with_scope<V: ExprVisitor>(
    expr: &KlujurVal,
    visitor: &mut V,
    bound: &HashSet<Symbol>,
) {
    match expr {
        KlujurVal::Symbol(sym, _) => {
            visitor.visit_symbol(sym);
        }
        KlujurVal::List(items, _) => {
            if items.is_empty() {
                return;
            }
            let items_vec: Vec<_> = items.iter().collect();
            let head = match &items_vec[0] {
                KlujurVal::Symbol(sym, _) => Some(sym.name()),
                _ => None,
            };

            visitor.visit_list(&items_vec, head);

            // Handle special forms
            if let Some(form) = head {
                if !visitor.should_descend(form) {
                    return;
                }

                match form {
                    "quote" => return, // Never descend into quotes
                    "fn" | "fn*" => {
                        walk_fn_form(&items_vec, visitor, bound);
                        return;
                    }
                    "let" | "let*" => {
                        walk_let_form(&items_vec, visitor, bound);
                        return;
                    }
                    "loop" => {
                        walk_loop_form(&items_vec, visitor, bound);
                        return;
                    }
                    "set!" => {
                        // Handle set! specially - visit target as symbol, then walk value
                        if let Some(KlujurVal::Symbol(target, _)) = items_vec.get(1) {
                            visitor.visit_symbol(target);
                        }
                        if let Some(val) = items_vec.get(2) {
                            walk_expr_with_scope(val, visitor, bound);
                        }
                        return;
                    }
                    _ => {}
                }
            }

            // Generic list: walk all elements
            for item in items_vec {
                walk_expr_with_scope(item, visitor, bound);
            }
        }
        KlujurVal::Vector(items, _) => {
            visitor.visit_vector(items);
            for item in items.iter() {
                walk_expr_with_scope(item, visitor, bound);
            }
        }
        KlujurVal::Map(map, _) => {
            visitor.visit_map(map);
            for (k, v) in map.iter() {
                walk_expr_with_scope(k, visitor, bound);
                walk_expr_with_scope(v, visitor, bound);
            }
        }
        KlujurVal::Set(set, _) => {
            visitor.visit_set(set);
            for item in set.iter() {
                walk_expr_with_scope(item, visitor, bound);
            }
        }
        _ => {} // Literals - nothing to visit
    }
}

/// Walk a fn/fn* form with proper scope handling.
fn walk_fn_form<V: ExprVisitor>(items: &[&KlujurVal], visitor: &mut V, bound: &HashSet<Symbol>) {
    // Parse fn structure: (fn [params] body...) or (fn name [params] body...)
    let (params_idx, body_start) = if items.len() > 1 {
        if let KlujurVal::Symbol(_, _) = &items[1] {
            (2, 3) // Named fn
        } else {
            (1, 2) // Anonymous fn
        }
    } else {
        return;
    };

    let mut fn_bound = bound.clone();
    let mut new_bindings = Vec::new();

    // Add fn name if present
    if params_idx == 2
        && let KlujurVal::Symbol(name, _) = &items[1]
    {
        fn_bound.insert(name.clone());
        new_bindings.push(name.clone());
    }

    // Add parameters to bound
    if let Some(KlujurVal::Vector(params, _)) = items.get(params_idx) {
        for p in params.iter() {
            if let KlujurVal::Symbol(s, _) = p
                && s.name() != "&"
            {
                fn_bound.insert(s.clone());
                new_bindings.push(s.clone());
            }
        }
    }

    visitor.enter_scope(&new_bindings);

    // Walk body
    for item in items.iter().skip(body_start) {
        walk_expr_with_scope(item, visitor, &fn_bound);
    }

    visitor.exit_scope(&new_bindings);
}

/// Walk a let/let* form with proper scope handling.
fn walk_let_form<V: ExprVisitor>(items: &[&KlujurVal], visitor: &mut V, bound: &HashSet<Symbol>) {
    let mut let_bound = bound.clone();
    let mut new_bindings = Vec::new();

    if let Some(KlujurVal::Vector(bindings, _)) = items.get(1) {
        let pairs: Vec<_> = bindings.iter().collect();
        for chunk in pairs.chunks(2) {
            if chunk.len() == 2 {
                // Walk value expression with current bindings
                walk_expr_with_scope(chunk[1], visitor, &let_bound);
                // Then add binding
                if let KlujurVal::Symbol(s, _) = chunk[0] {
                    let_bound.insert(s.clone());
                    new_bindings.push(s.clone());
                }
            }
        }
    }

    visitor.enter_scope(&new_bindings);

    // Walk body
    for item in items.iter().skip(2) {
        walk_expr_with_scope(item, visitor, &let_bound);
    }

    visitor.exit_scope(&new_bindings);
}

/// Walk a loop form with proper scope handling.
fn walk_loop_form<V: ExprVisitor>(items: &[&KlujurVal], visitor: &mut V, bound: &HashSet<Symbol>) {
    let mut loop_bound = bound.clone();
    let mut new_bindings = Vec::new();

    if let Some(KlujurVal::Vector(bindings, _)) = items.get(1) {
        let pairs: Vec<_> = bindings.iter().collect();
        for chunk in pairs.chunks(2) {
            if chunk.len() == 2 {
                walk_expr_with_scope(chunk[1], visitor, &loop_bound);
                if let KlujurVal::Symbol(s, _) = chunk[0] {
                    loop_bound.insert(s.clone());
                    new_bindings.push(s.clone());
                }
            }
        }
    }

    visitor.enter_scope(&new_bindings);

    // Walk body
    for item in items.iter().skip(2) {
        walk_expr_with_scope(item, visitor, &loop_bound);
    }

    visitor.exit_scope(&new_bindings);
}

// ============================================================================
// Concrete Visitor Implementations
// ============================================================================

/// Collects free variables referenced in an expression.
pub struct FreeVarCollector {
    bound: HashSet<Symbol>,
    pub free_vars: Vec<Symbol>,
}

impl FreeVarCollector {
    pub fn new(initial_bound: HashSet<Symbol>) -> Self {
        Self {
            bound: initial_bound,
            free_vars: Vec::new(),
        }
    }

    pub fn collect(expr: &KlujurVal, bound: HashSet<Symbol>) -> Vec<Symbol> {
        let mut collector = Self::new(bound);
        walk_expr(expr, &mut collector);
        collector.free_vars
    }
}

impl ExprVisitor for FreeVarCollector {
    fn visit_symbol(&mut self, sym: &Symbol) {
        if !self.bound.contains(sym) && !self.free_vars.contains(sym) {
            self.free_vars.push(sym.clone());
        }
    }

    fn enter_scope(&mut self, bindings: &[Symbol]) {
        for sym in bindings {
            self.bound.insert(sym.clone());
        }
    }

    fn exit_scope(&mut self, bindings: &[Symbol]) {
        for sym in bindings {
            self.bound.remove(sym);
        }
    }
}

/// Collects variables that are targets of set! expressions.
pub struct SetTargetCollector {
    pub mutated: HashSet<Symbol>,
}

impl SetTargetCollector {
    pub fn new() -> Self {
        Self {
            mutated: HashSet::new(),
        }
    }

    pub fn collect(expr: &KlujurVal) -> HashSet<Symbol> {
        let mut collector = Self::new();
        walk_expr(expr, &mut collector);
        collector.mutated
    }
}

impl Default for SetTargetCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl ExprVisitor for SetTargetCollector {
    fn visit_list(&mut self, items: &[&KlujurVal], head: Option<&str>) {
        // Record set! targets
        if head == Some("set!")
            && let Some(KlujurVal::Symbol(target, _)) = items.get(1)
        {
            self.mutated.insert(target.clone());
        }
    }

    fn should_descend(&self, form: &str) -> bool {
        // Don't descend into nested fn forms - they have their own set targets
        form != "fn" && form != "fn*"
    }
}

/// Collects local variables that need to be boxed (stored in heap cells).
/// A local needs boxing if it's captured by a nested function AND mutated.
pub struct BoxedLocalCollector {
    pub boxed: HashSet<Symbol>,
    mutated: HashSet<Symbol>,
}

impl BoxedLocalCollector {
    pub fn new(mutated: HashSet<Symbol>) -> Self {
        Self {
            boxed: HashSet::new(),
            mutated,
        }
    }

    /// Collect boxed locals from an expression.
    /// `mutated` should contain the set of variables that are targets of set!.
    pub fn collect(expr: &KlujurVal, mutated: HashSet<Symbol>) -> HashSet<Symbol> {
        let mut collector = Self::new(mutated);
        walk_expr(expr, &mut collector);
        collector.boxed
    }
}

impl ExprVisitor for BoxedLocalCollector {
    fn visit_list(&mut self, items: &[&KlujurVal], head: Option<&str>) {
        // When we see a nested fn, check if it captures any mutated variables
        if head == Some("fn") || head == Some("fn*") {
            // Scan the nested fn body for references to mutated variables
            // (without descending into its own nested fns)
            for item in items.iter().skip(1) {
                self.scan_for_mutated_refs(item);
            }
        }
    }

    fn should_descend(&self, form: &str) -> bool {
        // Don't automatically descend into nested fns - we handle them specially
        form != "fn" && form != "fn*"
    }
}

impl BoxedLocalCollector {
    /// Scan an expression for references to mutated variables.
    fn scan_for_mutated_refs(&mut self, expr: &KlujurVal) {
        match expr {
            KlujurVal::Symbol(sym, _) => {
                if self.mutated.contains(sym) {
                    self.boxed.insert(sym.clone());
                }
            }
            KlujurVal::List(items, _) => {
                let items_vec: Vec<_> = items.iter().collect();
                if let Some(KlujurVal::Symbol(sym, _)) = items_vec.first() {
                    let name = sym.name();
                    if name == "quote" || name == "fn" || name == "fn*" {
                        return;
                    }
                }
                for item in items_vec {
                    self.scan_for_mutated_refs(item);
                }
            }
            KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    self.scan_for_mutated_refs(item);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    self.scan_for_mutated_refs(k);
                    self.scan_for_mutated_refs(v);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    self.scan_for_mutated_refs(item);
                }
            }
            _ => {}
        }
    }
}
