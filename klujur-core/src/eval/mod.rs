// klujur-core - AST-walking evaluator
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! AST-walking evaluator for Klujur expressions.

// KlujurVal contains interior-mutable types (Var, Atom, Delay, Volatile) but hashes
// by identity/qualified-name, not mutable contents. This is intentional and safe.
#![allow(clippy::mutable_key_type)]

// Submodules
pub mod apply;
pub mod destructuring;
mod dynamic;
pub mod exceptions;
mod multimethods;
mod namespaces;
mod protocols;
mod records;
pub mod special_forms;

// Re-exports from submodules
pub use apply::{NativeFnImpl, apply, make_native_fn};
pub use destructuring::destructure;

use std::any::Any;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

use klujur_parser::{Keyword, KlujurFn, KlujurVal, Meta, Symbol};
use klujur_vm::chunk::{BytecodeFn, BytecodeFnWrapper};
use klujur_vm::compiler::analysis::Analyser;
use klujur_vm::compiler::codegen::Compiler as BytecodeCompiler;

use crate::namespace::NamespaceRegistry;

// ============================================================================
// Stack Overflow Protection
// ============================================================================

/// Maximum recursion depth for eval. Can be configured via `set_max_eval_depth`.
const DEFAULT_MAX_EVAL_DEPTH: usize = 10_000;

thread_local! {
    static EVAL_DEPTH: Cell<usize> = const { Cell::new(0) };
    static MAX_EVAL_DEPTH: Cell<usize> = const { Cell::new(DEFAULT_MAX_EVAL_DEPTH) };
    /// When true, functions are compiled to bytecode instead of being interpreted.
    static USE_BYTECODE: Cell<bool> = const { Cell::new(false) };
    /// Reference to the current namespace registry for bytecode global resolution.
    static CURRENT_REGISTRY: RefCell<Option<NamespaceRegistry>> = const { RefCell::new(None) };
}

/// Set the maximum eval recursion depth. Returns the previous value.
#[inline]
#[must_use]
pub fn set_max_eval_depth(depth: usize) -> usize {
    MAX_EVAL_DEPTH.with(|d| d.replace(depth))
}

/// Get the current maximum eval recursion depth.
#[inline]
#[must_use]
pub fn get_max_eval_depth() -> usize {
    MAX_EVAL_DEPTH.with(|d| d.get())
}

/// Get the current eval recursion depth.
#[inline]
#[must_use]
pub fn get_eval_depth() -> usize {
    EVAL_DEPTH.with(|d| d.get())
}

// ============================================================================
// Bytecode Compilation Mode
// ============================================================================

/// Enable or disable bytecode compilation mode. Returns the previous value.
///
/// When bytecode mode is enabled, simple functions (single-arity, no destructuring)
/// are compiled to bytecode and executed by the VM. More complex functions
/// continue to use the AST-walking interpreter.
#[inline]
#[must_use]
pub fn set_bytecode_mode(enabled: bool) -> bool {
    USE_BYTECODE.with(|b| b.replace(enabled))
}

/// Check if bytecode compilation mode is enabled.
#[inline]
#[must_use]
pub fn is_bytecode_mode() -> bool {
    USE_BYTECODE.with(|b| b.get())
}

/// Set the namespace registry for bytecode global resolution.
/// This should be called before evaluating any code in bytecode mode.
pub fn set_bytecode_registry(registry: NamespaceRegistry) {
    CURRENT_REGISTRY.with(|r| {
        *r.borrow_mut() = Some(registry);
    });

    // Set up the global resolver for the VM
    let resolver: Rc<klujur_vm::GlobalResolver> = Rc::new(resolve_bytecode_global);
    klujur_vm::set_global_resolver(Some(resolver));

    // Set up the function caller for native/interpreted functions
    let caller: Rc<klujur_vm::FnCaller> = Rc::new(call_bytecode_fn);
    klujur_vm::set_fn_caller(Some(caller));
}

/// Clear the bytecode registry.
pub fn clear_bytecode_registry() {
    CURRENT_REGISTRY.with(|r| {
        *r.borrow_mut() = None;
    });
    klujur_vm::set_global_resolver(None);
    klujur_vm::set_fn_caller(None);
}

/// Call a function from bytecode execution.
/// This handles native functions, interpreted functions, and other callable types.
fn call_bytecode_fn(
    func: &KlujurVal,
    args: &[KlujurVal],
) -> std::result::Result<KlujurVal, String> {
    apply::apply(func, args).map_err(|e| e.to_string())
}

/// Resolve a global variable for bytecode execution.
/// Handles both unqualified names ("foo") and qualified names ("ns/foo").
fn resolve_bytecode_global(name: &str) -> Option<KlujurVal> {
    CURRENT_REGISTRY.with(|r| {
        let registry_opt = r.borrow();
        let registry = registry_opt.as_ref()?;

        // Parse the symbol (handles both qualified and unqualified)
        let sym = Symbol::parse(name);
        let current_ns = registry.current();

        // Use resolve to handle aliases and refers
        if let Some(var) = current_ns.resolve(&sym) {
            return Some(crate::bindings::deref_var(&var));
        }

        // For qualified symbols, also try looking up the namespace directly
        if let Some(ns_name) = sym.namespace()
            && let Some(ns) = registry.find(ns_name)
            && let Some(var) = ns.find_var(sym.name())
        {
            return Some(crate::bindings::deref_var(&var));
        }

        // Fall back to klujur.core for builtins
        if let Some(core_ns) = registry.find(NamespaceRegistry::CORE_NS)
            && let Some(var) = core_ns.find_var(sym.name())
        {
            return Some(crate::bindings::deref_var(&var));
        }

        None
    })
}

/// RAII guard to manage eval depth counter.
struct EvalDepthGuard;

impl EvalDepthGuard {
    fn new() -> Result<Self> {
        let (current, max) = EVAL_DEPTH.with(|d| {
            let current = d.get();
            d.set(current + 1);
            (current + 1, MAX_EVAL_DEPTH.with(|m| m.get()))
        });
        if current > max {
            EVAL_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            Err(Error::EvalError(format!(
                "Stack overflow: maximum recursion depth ({}) exceeded",
                max
            )))
        } else {
            Ok(EvalDepthGuard)
        }
    }
}

impl Drop for EvalDepthGuard {
    fn drop(&mut self) {
        EVAL_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

use crate::bindings::deref_var;
use crate::env::Env;
use crate::error::{Error, Result};

// Import from submodules for internal use
use apply::apply_fn;
use dynamic::{
    eval_binding, eval_delay, eval_force, eval_lazy_seq, eval_reset, eval_reset_vals,
    eval_set_bang, eval_swap, eval_swap_vals,
};
use exceptions::{eval_throw, eval_try};
use multimethods::{
    eval_ancestors, eval_defmethod, eval_defmulti, eval_derive, eval_descendants, eval_isa,
    eval_parents, eval_underive,
};
use namespaces::{
    eval_alias, eval_all_ns, eval_create_ns, eval_find_ns, eval_in_ns, eval_ns_interns,
    eval_ns_name, eval_ns_publics, eval_ns_resolve, eval_refer, eval_remove_ns, eval_require,
    eval_resolve, eval_the_ns, eval_use, eval_var,
};
use protocols::{eval_defprotocol, eval_extend, eval_extend_type};
use records::eval_defrecord;
use special_forms::{
    eval_and, eval_as_thread, eval_cond, eval_eval, eval_if_not, eval_load_file, eval_load_string,
    eval_or, eval_thread_first, eval_thread_last, eval_time, eval_when, eval_when_not,
};

/// Convert a lazy seq to a list for evaluation (e.g., in macro expansion).
/// Non-lazy-seq values are returned as-is.
fn realize_for_eval(val: KlujurVal) -> Result<KlujurVal> {
    match val {
        KlujurVal::LazySeq(ls) => {
            // Force the lazy seq and collect into a list
            let items = crate::builtins::to_seq(&KlujurVal::LazySeq(ls))?;
            Ok(KlujurVal::list(items))
        }
        other => Ok(other),
    }
}

/// Evaluate a Klujur expression in the given environment.
///
/// This is the main entry point for interpreting Klujur code. It handles
/// all expression types including special forms, function application,
/// and symbol resolution.
///
/// # Examples
///
/// ```
/// use klujur_core::{Env, eval, register_builtins};
/// use klujur_parser::{KlujurVal, Parser};
///
/// let env = Env::new();
/// register_builtins(&env);
///
/// // Evaluate arithmetic
/// let mut parser = Parser::new("(* 6 7)").unwrap();
/// let expr = parser.parse().unwrap().unwrap();
/// let result = eval(&expr, &env).unwrap();
/// assert_eq!(result, KlujurVal::int(42));
///
/// // Evaluate nested expressions
/// let mut parser = Parser::new("(+ 1 (* 2 3))").unwrap();
/// let expr = parser.parse().unwrap().unwrap();
/// let result = eval(&expr, &env).unwrap();
/// assert_eq!(result, KlujurVal::int(7));
/// ```
///
/// # Errors
///
/// Returns an error if:
/// - A symbol cannot be resolved
/// - A function is called with wrong arity
/// - Type mismatches occur during operations
/// - Stack overflow occurs (configurable via [`set_max_eval_depth`])
#[must_use = "eval returns a value that should be used"]
pub fn eval(expr: &KlujurVal, env: &Env) -> Result<KlujurVal> {
    // Check recursion depth to prevent stack overflow
    let _guard = EvalDepthGuard::new()?;

    match expr {
        // Self-evaluating forms
        KlujurVal::Nil
        | KlujurVal::Bool(_)
        | KlujurVal::Int(_)
        | KlujurVal::BigInt(_)
        | KlujurVal::Float(_)
        | KlujurVal::Ratio(_, _)
        | KlujurVal::BigRatio(_, _)
        | KlujurVal::Char(_)
        | KlujurVal::String(_)
        | KlujurVal::Keyword(_)
        | KlujurVal::Fn(_)
        | KlujurVal::NativeFn(_)
        | KlujurVal::Macro(_)
        | KlujurVal::Atom(_)
        | KlujurVal::Delay(_)
        | KlujurVal::LazySeq(_)
        | KlujurVal::Multimethod(_)
        | KlujurVal::Hierarchy(_)
        | KlujurVal::Reduced(_)
        | KlujurVal::Volatile(_)
        | KlujurVal::Protocol(_)
        | KlujurVal::Record(_)
        | KlujurVal::Chunk(_)
        | KlujurVal::ChunkBuffer(_)
        | KlujurVal::ChunkedSeq(_) => Ok(expr.clone()),

        // Symbol lookup - automatically dereferences Vars
        KlujurVal::Symbol(sym, _) => {
            // Special handling for *ns* - returns the current namespace as a symbol
            if sym.name() == "*ns*" && sym.namespace().is_none() {
                let registry = env.registry();
                let current_ns = registry.current();
                return Ok(KlujurVal::symbol(Symbol::new(&current_ns.name())));
            }

            // Check if this is a qualified symbol (ns/name)
            if let Some(ns_name) = sym.namespace() {
                // Qualified symbol - resolve through namespace registry
                let registry = env.registry();
                let current_ns = registry.current();
                let current_ns_name = current_ns.name();

                // First, try to resolve via the current namespace (which checks aliases)
                if let Some(var) = current_ns.resolve(sym) {
                    // Check privacy: error if accessing private var from different namespace
                    let var_ns = var.ns.clone().unwrap_or_default();
                    if !var.is_public() && var_ns != current_ns_name {
                        return Err(Error::EvalError(format!(
                            "var: {}/{} is not public",
                            ns_name,
                            sym.name()
                        )));
                    }
                    return Ok(deref_var(&var));
                }

                // Then try to look up the namespace directly by name
                if let Some(ns) = registry.find(ns_name) {
                    // Find the var in that namespace
                    if let Some(var) = ns.find_var(sym.name()) {
                        // Check privacy: error if accessing private var from different namespace
                        if !var.is_public() && ns_name != current_ns_name {
                            return Err(Error::EvalError(format!(
                                "var: {}/{} is not public",
                                ns_name,
                                sym.name()
                            )));
                        }
                        return Ok(deref_var(&var));
                    }
                }
                // Fall through to normal lookup if not found
            }

            // Try lexical environment first
            match env.lookup(sym) {
                Ok(val) => {
                    // Auto-deref Vars to get the value (checking thread bindings)
                    match val {
                        KlujurVal::Var(v) => Ok(deref_var(&v)),
                        other => Ok(other),
                    }
                }
                Err(_) => {
                    // Not in lexical env, try namespace registry (current ns + refers)
                    let registry = env.registry();
                    let current_ns = registry.current();
                    if let Some(var) = current_ns.resolve(sym) {
                        return Ok(deref_var(&var));
                    }
                    Err(Error::UndefinedSymbol(sym.clone()))
                }
            }
        }

        // List - either special form or function call
        KlujurVal::List(items, _) => {
            let items_vec: Vec<KlujurVal> = items.iter().cloned().collect();
            eval_list(&items_vec, env)
        }

        // Vectors evaluate their elements
        KlujurVal::Vector(items, _) => {
            let evaluated: Result<Vec<_>> = items.iter().map(|e| eval(e, env)).collect();
            Ok(KlujurVal::vector(evaluated?))
        }

        // Maps evaluate their keys and values
        KlujurVal::Map(map, _) => {
            let mut result = Vec::with_capacity(map.len());
            for (k, v) in map.iter() {
                result.push((eval(k, env)?, eval(v, env)?));
            }
            Ok(KlujurVal::map(result))
        }

        // Sets evaluate their elements
        KlujurVal::Set(items, _) => {
            let evaluated: Result<Vec<_>> = items.iter().map(|e| eval(e, env)).collect();
            Ok(KlujurVal::set(evaluated?))
        }

        // Vars dereference to their value (checking thread bindings)
        KlujurVal::Var(v) => Ok(deref_var(v)),

        // Sorted collections are self-evaluating
        KlujurVal::SortedMapBy(_) | KlujurVal::SortedSetBy(_) => Ok(expr.clone()),

        // Custom values are self-evaluating
        KlujurVal::Custom(_) => Ok(expr.clone()),
    }
}

/// Look up a symbol in the lexical environment, falling back to namespace registry.
/// Returns the raw value (Var for vars, NativeFn for builtins, etc.).
fn lookup_symbol(sym: &Symbol, env: &Env) -> Result<KlujurVal> {
    // Try lexical environment first
    match env.lookup(sym) {
        Ok(val) => Ok(val),
        Err(_) => {
            // Not in lexical env, try namespace registry
            let registry = env.registry();
            let current_ns = registry.current();
            current_ns
                .resolve(sym)
                .map(KlujurVal::Var)
                .ok_or_else(|| Error::UndefinedSymbol(sym.clone()))
        }
    }
}

/// Evaluate a list form (special form or function call).
fn eval_list(items: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if items.is_empty() {
        // Empty list evaluates to itself
        return Ok(KlujurVal::empty_list());
    }

    // Check for special forms
    if let KlujurVal::Symbol(sym, _) = &items[0] {
        match sym.name() {
            "quote" => return eval_quote(&items[1..]),
            "syntax-quote" => return eval_syntax_quote(&items[1..], env),
            "if" => return eval_if(&items[1..], env),
            "do" => return eval_do(&items[1..], env),
            "let" | "let*" => return eval_let(&items[1..], env),
            "def" => return eval_def(&items[1..], env),
            "fn" | "fn*" => return eval_fn(&items[1..], env),
            "loop" => return eval_loop(&items[1..], env),
            "recur" => return eval_recur(&items[1..], env),
            "and" => return eval_and(&items[1..], env),
            "or" => return eval_or(&items[1..], env),
            "when" => return eval_when(&items[1..], env),
            "when-not" => return eval_when_not(&items[1..], env),
            "if-not" => return eval_if_not(&items[1..], env),
            "cond" => return eval_cond(&items[1..], env),
            "->" => return eval_thread_first(&items[1..], env),
            "->>" => return eval_thread_last(&items[1..], env),
            "as->" => return eval_as_thread(&items[1..], env),
            "in-ns" => return eval_in_ns(&items[1..], env),
            "var" => return eval_var(&items[1..], env),
            "ns-publics" => return eval_ns_publics(&items[1..], env),
            "ns-interns" => return eval_ns_interns(&items[1..], env),
            "refer" => return eval_refer(&items[1..], env),
            "alias" => return eval_alias(&items[1..], env),
            "require" => return eval_require(&items[1..], env),
            "use" => return eval_use(&items[1..], env),
            "all-ns" => return eval_all_ns(&items[1..], env),
            "find-ns" => return eval_find_ns(&items[1..], env),
            "create-ns" => return eval_create_ns(&items[1..], env),
            "remove-ns" => return eval_remove_ns(&items[1..], env),
            "the-ns" => return eval_the_ns(&items[1..], env),
            "ns-name" => return eval_ns_name(&items[1..], env),
            "ns-resolve" => return eval_ns_resolve(&items[1..], env),
            "resolve" => return eval_resolve(&items[1..], env),
            "defmacro" => return eval_defmacro(&items[1..], env),
            "macroexpand-1" => return eval_macroexpand_1(&items[1..], env),
            "macroexpand" => return eval_macroexpand(&items[1..], env),
            "throw" => return eval_throw(&items[1..], env),
            "try" => return eval_try(&items[1..], env),
            "binding" => return eval_binding(&items[1..], env),
            "set!" => return eval_set_bang(&items[1..], env),
            "swap!" => return eval_swap(&items[1..], env),
            "swap-vals!" => return eval_swap_vals(&items[1..], env),
            "reset!" => return eval_reset(&items[1..], env),
            "reset-vals!" => return eval_reset_vals(&items[1..], env),
            "delay" => return eval_delay(&items[1..], env),
            "force" => return eval_force(&items[1..], env),
            "lazy-seq" => return eval_lazy_seq(&items[1..], env),
            "time" => return eval_time(&items[1..], env),
            "eval" => return eval_eval(&items[1..], env),
            "load-string" => return eval_load_string(&items[1..], env),
            "load-file" => return eval_load_file(&items[1..], env),
            "defmulti" => return eval_defmulti(&items[1..], env),
            "defmethod" => return eval_defmethod(&items[1..], env),
            "derive" => return eval_derive(&items[1..], env),
            "underive" => return eval_underive(&items[1..], env),
            "isa?" => return eval_isa(&items[1..], env),
            "parents" => return eval_parents(&items[1..], env),
            "ancestors" => return eval_ancestors(&items[1..], env),
            "descendants" => return eval_descendants(&items[1..], env),
            "defprotocol" => return eval_defprotocol(&items[1..], env),
            "extend-type" => return eval_extend_type(&items[1..], env),
            "extend" => return eval_extend(&items[1..], env),
            "defrecord" => return eval_defrecord(&items[1..], env),
            _ => {}
        }
    }

    // Check if this is a macro call - if so, expand before evaluating
    // First, evaluate just the operator to see if it's a macro
    let op = eval(&items[0], env)?;

    if let KlujurVal::Macro(m) = &op {
        // Macro call - pass unevaluated args, then eval the result
        let expanded = apply_fn(m, &items[1..])?;
        // If the macro returns a lazy seq, convert it to a list for evaluation
        let expanded = realize_for_eval(expanded)?;
        return eval(&expanded, env);
    }

    // Regular function call - evaluate all forms then apply
    let mut evaluated = vec![op];
    for item in &items[1..] {
        match eval(item, env) {
            Ok(val) => evaluated.push(val),
            Err(Error::Recur(_)) => {
                // recur was called in a non-tail position (as an argument to a function)
                return Err(Error::syntax("recur", "can only appear in tail position"));
            }
            Err(e) => return Err(e),
        }
    }
    apply(&evaluated[0], &evaluated[1..])
}

// ============================================================================
// Special Forms
// ============================================================================

/// (quote form) - return form unevaluated
fn eval_quote(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("quote", "requires exactly 1 argument"));
    }
    Ok(args[0].clone())
}

/// (syntax-quote form) - quote with unquoting and auto-gensym support
/// Handles:
///   `form - quotes form
///   ~expr - evaluates expr (unquote)
///   ~@expr - evaluates and splices expr (unquote-splicing)
///   sym# - generates unique symbol (auto-gensym)
fn eval_syntax_quote(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use std::collections::HashMap;

    if args.len() != 1 {
        return Err(Error::syntax("syntax-quote", "requires exactly 1 argument"));
    }

    // Track gensyms across the form for consistent naming
    let mut gensyms: HashMap<String, Symbol> = HashMap::new();
    let mut counter = 0;

    fn process(
        form: &KlujurVal,
        env: &Env,
        gensyms: &mut HashMap<String, Symbol>,
        counter: &mut u64,
    ) -> Result<KlujurVal> {
        match form {
            // Handle unquote: (unquote x) -> evaluate x
            KlujurVal::List(items, _) => {
                let items_vec: Vec<_> = items.iter().cloned().collect();
                if let Some(KlujurVal::Symbol(sym, _)) = items_vec.first() {
                    if sym.name() == "unquote" {
                        if items_vec.len() != 2 {
                            return Err(Error::syntax("unquote", "requires exactly 1 argument"));
                        }
                        return eval(&items_vec[1], env);
                    }
                    if sym.name() == "unquote-splicing" {
                        return Err(Error::syntax(
                            "unquote-splicing",
                            "can only be used inside a list",
                        ));
                    }
                }

                // Process list elements, handling unquote-splicing
                let mut result = Vec::new();
                for item in &items_vec {
                    if let KlujurVal::List(inner, _) = item
                        && let Some(KlujurVal::Symbol(sym, _)) = inner.iter().next()
                        && sym.name() == "unquote-splicing"
                    {
                        let inner_vec: Vec<_> = inner.iter().cloned().collect();
                        if inner_vec.len() != 2 {
                            return Err(Error::syntax(
                                "unquote-splicing",
                                "requires exactly 1 argument",
                            ));
                        }
                        let spliced = eval(&inner_vec[1], env)?;
                        match spliced {
                            KlujurVal::List(l, _) => result.extend(l.iter().cloned()),
                            KlujurVal::Vector(v, _) => result.extend(v.iter().cloned()),
                            KlujurVal::Nil => {}
                            KlujurVal::LazySeq(ls) => {
                                // Force lazy sequence and splice elements
                                let items = crate::builtins::to_seq(&KlujurVal::LazySeq(ls))?;
                                result.extend(items);
                            }
                            other => {
                                return Err(Error::syntax(
                                    "unquote-splicing",
                                    format!("expected sequence, got {}", other.type_name()),
                                ));
                            }
                        }
                        continue;
                    }
                    result.push(process(item, env, gensyms, counter)?);
                }
                Ok(KlujurVal::list(result))
            }

            // Handle vectors similarly
            KlujurVal::Vector(items, _) => {
                let mut result = Vec::new();
                for item in items.iter() {
                    if let KlujurVal::List(inner, _) = item
                        && let Some(KlujurVal::Symbol(sym, _)) = inner.iter().next()
                        && sym.name() == "unquote-splicing"
                    {
                        let inner_vec: Vec<_> = inner.iter().cloned().collect();
                        if inner_vec.len() != 2 {
                            return Err(Error::syntax(
                                "unquote-splicing",
                                "requires exactly 1 argument",
                            ));
                        }
                        let spliced = eval(&inner_vec[1], env)?;
                        match spliced {
                            KlujurVal::List(l, _) => result.extend(l.iter().cloned()),
                            KlujurVal::Vector(v, _) => result.extend(v.iter().cloned()),
                            KlujurVal::Nil => {}
                            KlujurVal::LazySeq(ls) => {
                                // Force lazy sequence and splice elements
                                let items = crate::builtins::to_seq(&KlujurVal::LazySeq(ls))?;
                                result.extend(items);
                            }
                            other => {
                                return Err(Error::syntax(
                                    "unquote-splicing",
                                    format!("expected sequence, got {}", other.type_name()),
                                ));
                            }
                        }
                        continue;
                    }
                    result.push(process(item, env, gensyms, counter)?);
                }
                Ok(KlujurVal::vector(result))
            }

            // Handle maps
            KlujurVal::Map(map, _) => {
                let mut result = Vec::new();
                for (k, v) in map.iter() {
                    result.push((
                        process(k, env, gensyms, counter)?,
                        process(v, env, gensyms, counter)?,
                    ));
                }
                Ok(KlujurVal::map(result))
            }

            // Handle sets
            KlujurVal::Set(set, _) => {
                let mut result = Vec::new();
                for item in set.iter() {
                    result.push(process(item, env, gensyms, counter)?);
                }
                Ok(KlujurVal::set(result))
            }

            // Handle auto-gensym symbols (ending in #)
            KlujurVal::Symbol(sym, _) if sym.name().ends_with('#') && sym.namespace().is_none() => {
                let name = sym.name();
                if let Some(existing) = gensyms.get(name) {
                    Ok(KlujurVal::Symbol(existing.clone(), None))
                } else {
                    let base = &name[..name.len() - 1];
                    let gensym = Symbol::new(&format!("{}__auto__{}", base, *counter));
                    *counter += 1;
                    gensyms.insert(name.to_string(), gensym.clone());
                    Ok(KlujurVal::Symbol(gensym, None))
                }
            }

            // Handle unqualified symbols - auto-qualify with the namespace where they resolve
            // EXCEPT for special forms which should remain unqualified
            KlujurVal::Symbol(sym, meta) if sym.namespace().is_none() => {
                let name = sym.name();
                // Special forms that should NOT be qualified
                const SPECIAL_FORMS: &[&str] = &[
                    "if",
                    "do",
                    "let*",
                    "def",
                    "fn*",
                    "loop",
                    "recur",
                    "quote",
                    "var",
                    "try",
                    "catch",
                    "finally",
                    "throw",
                    "binding",
                    "defmacro",
                    "in-ns",
                    "ns",
                    "require",
                    "use",
                    "refer",
                    "alias",
                    "import",
                    "defmulti",
                    "defmethod",
                    "defprotocol",
                    "extend-type",
                    "extend",
                    "defrecord",
                    "new",
                    "set!",
                    ".",
                    "..",
                    "->",
                    "->>",
                    "as->",
                    "cond",
                    "case",
                    "when",
                    "when-not",
                    "when-let",
                    "when-some",
                    "if-let",
                    "if-some",
                    "if-not",
                    "and",
                    "or",
                    "not",
                    "for",
                    "doseq",
                    "dotimes",
                    "while",
                    "delay",
                    "lazy-seq",
                    "force",
                    "derive",
                    "underive",
                    "isa?",
                    "parents",
                    "ancestors",
                    "descendants",
                    "swap!",
                    "reset!",
                    "swap-vals!",
                    "compare-and-set!",
                    "unquote",
                    "unquote-splicing",
                    "macroexpand",
                    "macroexpand-1",
                    "eval",
                    "load-file",
                    "load-string",
                    "time",
                    "assert",
                    "comment",
                    "declare",
                ];
                if SPECIAL_FORMS.contains(&name) {
                    // Don't qualify special forms
                    Ok(form.clone())
                } else {
                    // Try to resolve the symbol to find its home namespace
                    let registry = env.registry();
                    let current_ns = registry.current();
                    let ns_name = if let Some(var) = current_ns.resolve(sym) {
                        // Symbol resolves - use the var's namespace
                        var.ns
                            .clone()
                            .unwrap_or_else(|| registry.current_name().to_string())
                    } else {
                        // Symbol doesn't resolve - qualify with current namespace
                        registry.current_name().to_string()
                    };
                    let qualified = Symbol::with_namespace(&ns_name, name);
                    Ok(KlujurVal::Symbol(qualified, meta.clone()))
                }
            }

            // Everything else is returned as-is (quoted)
            other => Ok(other.clone()),
        }
    }

    process(&args[0], env, &mut gensyms, &mut counter)
}

/// (if test then else?) - conditional evaluation
fn eval_if(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::syntax("if", "requires 2 or 3 arguments"));
    }

    let test = eval(&args[0], env)?;

    if test.is_truthy() {
        eval(&args[1], env)
    } else if args.len() == 3 {
        eval(&args[2], env)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (do exprs*) - evaluate expressions in sequence, return last
fn eval_do(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    let mut result = KlujurVal::Nil;
    for expr in args {
        result = eval(expr, env)?;
    }
    Ok(result)
}

/// (let* [bindings] body...) - local bindings with sequential evaluation
/// Supports destructuring: (let* [[a b] [1 2]] a) => 1
fn eval_let(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("let*", "requires a binding vector"));
    }

    let bindings: Vec<KlujurVal> = match &args[0] {
        KlujurVal::Vector(v, _) => v.iter().cloned().collect(),
        _ => {
            return Err(Error::syntax(
                "let*",
                "first argument must be a binding vector",
            ));
        }
    };

    if !bindings.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "let*",
            "binding vector must have even number of forms",
        ));
    }

    // Create child environment for let bindings
    let let_env = env.child();

    // Process bindings sequentially with destructuring support
    for pair in bindings.chunks(2) {
        let pattern = &pair[0];
        let val = eval(&pair[1], &let_env)?;

        // Destructure and add all bindings
        let binds = destructure(pattern, &val)?;
        for (sym, bound_val) in binds {
            let_env.define(sym, bound_val);
        }
    }

    // Evaluate body in let environment
    let body = &args[1..];
    let mut result = KlujurVal::Nil;
    for expr in body {
        result = eval(expr, &let_env)?;
    }
    Ok(result)
}

/// Extract a symbol and its metadata from a form.
///
/// This handles both direct symbols and the expanded metadata syntax.
/// For example:
/// - `x` returns (x, None)
/// - `(with-meta x {:private true})` returns (x, Some({:private true}))
/// - Stacked: `(with-meta (with-meta x {:b true}) {:a true})` returns (x, merged metadata)
fn extract_symbol_and_meta(form: &KlujurVal, env: &Env) -> Result<(Symbol, Option<Rc<Meta>>)> {
    match form {
        KlujurVal::Symbol(sym, meta) => Ok((sym.clone(), meta.clone())),
        KlujurVal::List(items, _) => {
            let items_vec: Vec<_> = items.iter().cloned().collect();
            // Check if this is a (with-meta sym meta) form
            if items_vec.len() == 3
                && let KlujurVal::Symbol(fn_sym, _) = &items_vec[0]
                && fn_sym.name() == "with-meta"
            {
                // Recursively extract from inner form (handles stacking)
                let (sym, inner_meta) = extract_symbol_and_meta(&items_vec[1], env)?;

                // Evaluate the metadata form
                let outer_meta_val = eval(&items_vec[2], env)?;

                // Convert to OrdMap
                let outer_meta = match outer_meta_val {
                    KlujurVal::Map(m, _) => m,
                    _ => {
                        return Err(Error::syntax("with-meta", "metadata must be a map"));
                    }
                };

                // Merge inner and outer metadata (outer takes precedence)
                let merged = if let Some(inner) = inner_meta {
                    let mut merged = (*inner).clone();
                    for (k, v) in outer_meta.iter() {
                        merged.insert(k.clone(), v.clone());
                    }
                    merged
                } else {
                    outer_meta
                };

                return Ok((sym, Some(Rc::new(merged))));
            }
            Err(Error::syntax(
                "def",
                format!("first argument must be a symbol, got {}", form.type_name()),
            ))
        }
        other => Err(Error::syntax(
            "def",
            format!("first argument must be a symbol, got {}", other.type_name()),
        )),
    }
}

/// (def name value) - define a var in the current environment
/// Uses "earmuffs" convention: vars named like `*name*` are dynamic.
/// Also applies any metadata from the symbol to the created var.
///
/// Supports metadata syntax: (def ^:private x 1)
/// which parses as (def (with-meta x {:private true}) 1)
fn eval_def(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() || args.len() > 2 {
        return Err(Error::syntax("def", "requires 1 or 2 arguments"));
    }

    // Extract symbol and metadata - handle both direct symbol and (with-meta sym meta)
    let (sym, sym_meta) = extract_symbol_and_meta(&args[0], env)?;

    // If only 1 arg, value is nil (creates unbound var); otherwise evaluate the second arg
    let val = if args.len() == 2 {
        eval(&args[1], env)?
    } else {
        KlujurVal::Nil
    };

    // Check for "earmuffs" convention: *name* indicates dynamic var
    // Also check for :dynamic metadata
    let dynamic_key = KlujurVal::keyword(Keyword::new("dynamic"));
    let is_dynamic = is_earmuffed(sym.name())
        || sym_meta
            .as_ref()
            .map(|m| m.get(&dynamic_key).is_some_and(|v| v.is_truthy()))
            .unwrap_or(false);

    // Create or update a Var in the current namespace
    let registry = env.registry();
    let current_ns = registry.current();
    let var = current_ns.intern_with_value(sym.name(), val);

    // Set the dynamic flag if using earmuffs convention or :dynamic metadata
    if is_dynamic {
        var.set_dynamic(true);
    }

    // Apply symbol metadata to the var
    if let Some(meta) = sym_meta {
        var.set_meta(Some((*meta).clone()));
    }

    // Return the Var (vars are stored in the namespace, not lexical env)
    Ok(KlujurVal::Var(var))
}

/// Check if a name follows the "earmuffs" convention (*name*).
fn is_earmuffed(name: &str) -> bool {
    name.len() >= 3 && name.starts_with('*') && name.ends_with('*')
}

/// (fn* [params] body...) or (fn* name [params] body...) - create function
/// (fn* ([p1] body1) ([p2 p3] body2)) or (fn* name ([p1] body1) ...) - multi-arity
/// Supports destructuring in parameters: (fn* [[a b]] (+ a b))
fn eval_fn(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::FnArity;

    if args.is_empty() {
        return Err(Error::syntax("fn*", "requires a parameter vector"));
    }

    // Check if first arg is a symbol (optional function name for self-recursion)
    let (fn_name, args) = if let KlujurVal::Symbol(sym, _) = &args[0] {
        (Some(sym.clone()), &args[1..])
    } else {
        (None, args)
    };

    if args.is_empty() {
        return Err(Error::syntax("fn*", "requires a parameter vector"));
    }

    // Check if first arg is a list (multi-arity) or vector (single-arity)
    let arities = if matches!(&args[0], KlujurVal::List(_, _)) {
        // Multi-arity: (fn* ([x] x) ([x y] (+ x y)))
        let mut arities = Vec::new();
        for arity_form in args {
            let arity_list: Vec<KlujurVal> = match arity_form {
                KlujurVal::List(items, _) => items.iter().cloned().collect(),
                _ => {
                    return Err(Error::syntax(
                        "fn*",
                        "each arity must be a list like ([params] body...)",
                    ));
                }
            };
            if arity_list.is_empty() {
                return Err(Error::syntax("fn*", "arity requires a parameter vector"));
            }
            let (params, rest, patterns, rest_pattern, body) =
                parse_fn_arity(&arity_list[0], &arity_list[1..])?;
            arities.push(FnArity::with_patterns(
                params,
                rest,
                patterns,
                rest_pattern,
                body,
            ));
        }
        arities
    } else {
        // Single-arity: (fn* [x] body)
        let (params, rest, patterns, rest_pattern, body) = parse_fn_arity(&args[0], &args[1..])?;
        vec![FnArity::with_patterns(
            params,
            rest,
            patterns,
            rest_pattern,
            body,
        )]
    };

    // Try bytecode compilation for simple functions
    if is_bytecode_mode()
        && can_compile_to_bytecode(&arities, &fn_name, args)
        && let Some(bytecode_fn) = try_compile_to_bytecode(&arities, &fn_name, args)
    {
        return Ok(KlujurVal::custom(BytecodeFnWrapper(Rc::new(bytecode_fn))));
    }

    // Create function value with type-erased environment
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let func = KlujurFn::new_multi(fn_name, arities, env_any);
    Ok(KlujurVal::Fn(func))
}

/// Check if a function can be compiled to bytecode.
/// Requirements:
/// - Single arity
/// - No destructuring patterns
fn can_compile_to_bytecode(
    arities: &[klujur_parser::FnArity],
    _fn_name: &Option<Symbol>,
    _args: &[KlujurVal],
) -> bool {
    // Only single-arity functions for now
    if arities.len() != 1 {
        return false;
    }

    let arity = &arities[0];

    // Rest parameters are now supported
    // if arity.rest_param.is_some() {
    //     return false;
    // }

    // No destructuring patterns
    if !arity.param_patterns.is_empty() || arity.rest_pattern.is_some() {
        return false;
    }

    true
}

/// Try to compile a function to bytecode.
/// Returns None if compilation fails (falls back to interpreter).
fn try_compile_to_bytecode(
    arities: &[klujur_parser::FnArity],
    fn_name: &Option<Symbol>,
    args: &[KlujurVal],
) -> Option<BytecodeFn> {
    use klujur_vm::VM;

    let arity = &arities[0];

    // Build the parameter vector from the parsed arity
    let mut params_vec: Vec<KlujurVal> = arity
        .params
        .iter()
        .map(|s| KlujurVal::Symbol(s.clone(), None))
        .collect();

    // Add rest parameter if present: [params... & rest]
    if let Some(rest_sym) = &arity.rest_param {
        params_vec.push(KlujurVal::Symbol(Symbol::new("&"), None));
        params_vec.push(KlujurVal::Symbol(rest_sym.clone(), None));
    }

    let params_val = KlujurVal::vector(params_vec);

    // Build the complete fn expression
    let mut fn_items = vec![KlujurVal::Symbol(Symbol::new("fn"), None)];
    if let Some(name) = fn_name {
        fn_items.push(KlujurVal::Symbol(name.clone(), None));
    }
    fn_items.push(params_val);

    // Add body - for single arity, body is after the params vector in args
    if matches!(&args[0], KlujurVal::Vector(_, _)) {
        fn_items.extend_from_slice(&args[1..]);
    }

    let fn_expr = KlujurVal::list(fn_items);

    // Compile the fn expression
    let mut analyser = Analyser::new();
    let analysis = analyser.analyse(&fn_expr);
    let compiler = BytecodeCompiler::new(analysis);

    match compiler.compile(&fn_expr) {
        Ok(chunk) => {
            // Run the chunk to get the BytecodeFn value
            let mut vm = VM::new();
            match vm.run(chunk) {
                Ok(val) => {
                    // Extract the BytecodeFn from the Custom value
                    if let KlujurVal::Custom(custom) = val
                        && let Some(wrapper) = custom.downcast_ref::<BytecodeFnWrapper>()
                    {
                        return Some((*wrapper.0).clone());
                    }
                    None
                }
                Err(_) => None,
            }
        }
        Err(_) => None,
    }
}

/// Result of parsing fn* parameters: (params, rest_param, param_patterns, rest_pattern, body)
pub(crate) type ParsedFnArity = (
    Vec<Symbol>,
    Option<Symbol>,
    Vec<KlujurVal>,
    Option<KlujurVal>,
    Vec<KlujurVal>,
);

/// Parse a parameter vector and body for fn*
/// Supports destructuring patterns in parameter position.
pub(crate) fn parse_fn_arity(
    params_form: &KlujurVal,
    body_forms: &[KlujurVal],
) -> Result<ParsedFnArity> {
    let params = match params_form {
        KlujurVal::Vector(v, _) => v.clone(),
        _ => {
            return Err(Error::syntax(
                "fn*",
                "first argument must be a parameter vector",
            ));
        }
    };

    let mut param_names = Vec::with_capacity(params.len());
    let mut param_patterns = Vec::with_capacity(params.len());
    let mut rest_param = None;
    let mut rest_pattern = None;
    let mut has_destructuring = false;
    let mut i = 0;

    while i < params.len() {
        let param = &params[i];

        // Check for & rest parameter
        if let KlujurVal::Symbol(s, _) = param
            && s.name() == "&"
        {
            // Rest parameter
            if i + 1 >= params.len() {
                return Err(Error::syntax("fn*", "& must be followed by a parameter"));
            }
            if i + 2 != params.len() {
                return Err(Error::syntax("fn*", "only one parameter after &"));
            }

            let rest_pat = &params[i + 1];
            match rest_pat {
                KlujurVal::Symbol(rest, _) => {
                    rest_param = Some(rest.clone());
                }
                KlujurVal::Vector(_, _) | KlujurVal::Map(_, _) => {
                    // Destructuring pattern for rest - use gensym
                    has_destructuring = true;
                    rest_param = Some(Symbol::new(&format!("__rest_{}", i)));
                    rest_pattern = Some(rest_pat.clone());
                }
                other => {
                    return Err(Error::syntax(
                        "fn*",
                        format!(
                            "rest parameter must be a symbol or pattern, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }
            break;
        }

        // Process regular parameter (may be symbol or destructuring pattern)
        match param {
            KlujurVal::Symbol(s, _) => {
                param_names.push(s.clone());
                param_patterns.push(param.clone());
            }
            KlujurVal::Vector(_, _) | KlujurVal::Map(_, _) => {
                // Destructuring pattern - create a gensym for the positional binding
                has_destructuring = true;
                let gensym = Symbol::new(&format!("__p{}", i));
                param_names.push(gensym);
                param_patterns.push(param.clone());
            }
            other => {
                return Err(Error::syntax(
                    "fn*",
                    format!(
                        "parameter must be a symbol or pattern, got {}",
                        other.type_name()
                    ),
                ));
            }
        }
        i += 1;
    }

    let body = body_forms.to_vec();

    // Only include patterns if there was actually destructuring
    if has_destructuring {
        Ok((param_names, rest_param, param_patterns, rest_pattern, body))
    } else {
        Ok((param_names, rest_param, Vec::new(), None, body))
    }
}

/// (loop [bindings] body...) - loop with recur support
/// Supports destructuring: (loop [[a b] [1 2]] (+ a b))
fn eval_loop(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("loop", "requires a binding vector"));
    }

    let bindings: Vec<KlujurVal> = match &args[0] {
        KlujurVal::Vector(v, _) => v.iter().cloned().collect(),
        _ => {
            return Err(Error::syntax(
                "loop",
                "first argument must be a binding vector",
            ));
        }
    };

    if !bindings.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "loop",
            "binding vector must have even number of forms",
        ));
    }

    // Extract binding patterns and initial values
    // For recur, we track both the patterns and a gensym for each position
    // Bindings are evaluated sequentially (like let*), so later bindings can
    // reference earlier ones.
    let mut binding_patterns: Vec<KlujurVal> = Vec::with_capacity(bindings.len() / 2);
    let mut binding_gensyms: Vec<Symbol> = Vec::with_capacity(bindings.len() / 2);
    let mut initial_values: Vec<KlujurVal> = Vec::with_capacity(bindings.len() / 2);

    // Create a temporary environment for sequential binding evaluation
    let init_env = env.child();

    for (i, pair) in bindings.chunks(2).enumerate() {
        let pattern = &pair[0];
        let val = eval(&pair[1], &init_env)?;

        // Create a gensym for recur tracking (or use the symbol directly if simple)
        let gensym = match pattern {
            KlujurVal::Symbol(s, _) => s.clone(),
            _ => Symbol::new(&format!("__loop_{}", i)),
        };

        // Add bindings to init_env so later bindings can reference earlier ones
        let binds = destructure(pattern, &val)?;
        for (sym, bound_val) in binds {
            init_env.define(sym, bound_val);
        }

        binding_patterns.push(pattern.clone());
        binding_gensyms.push(gensym);
        initial_values.push(val);
    }

    let body = &args[1..];
    let mut current_values = initial_values;
    let num_bindings = binding_patterns.len();

    // The actual loop - using Rust's loop for tail-call optimisation
    'outer: loop {
        // Create loop environment with current bindings
        let loop_env = env.child();

        // Destructure each pattern against its current value
        for (i, val) in current_values.iter().enumerate() {
            let pattern = &binding_patterns[i];
            let gensym = &binding_gensyms[i];

            // Bind the gensym to the raw value (for potential nested recur tracking)
            loop_env.define(gensym.clone(), val.clone());

            // Destructure the pattern
            let binds = destructure(pattern, val)?;
            for (sym, bound_val) in binds {
                loop_env.define(sym, bound_val);
            }
        }

        // Evaluate body expressions
        let mut result = KlujurVal::Nil;
        for (i, expr) in body.iter().enumerate() {
            let is_last = i == body.len() - 1;
            match eval(expr, &loop_env) {
                Ok(val) => {
                    result = val;
                }
                Err(Error::Recur(new_values)) => {
                    if !is_last {
                        return Err(Error::syntax("recur", "can only appear in tail position"));
                    }
                    if new_values.len() != num_bindings {
                        return Err(Error::ArityError {
                            expected: crate::error::AritySpec::Exact(num_bindings),
                            got: new_values.len(),
                            name: Some("recur".to_string()),
                        });
                    }
                    current_values = new_values;
                    continue 'outer;
                }
                Err(e) => return Err(e),
            }
        }

        // If we get here without a recur, return the result
        return Ok(result);
    }
}

/// (recur exprs...) - recur to enclosing loop or fn
fn eval_recur(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Evaluate all arguments
    let values: Result<Vec<_>> = args.iter().map(|e| eval(e, env)).collect();
    Err(Error::Recur(values?))
}

/// (defmacro name docstring? [params] body...) - define a macro
/// (defmacro name docstring? ([params] body...) ([params2] body2...)) - multi-arity
fn eval_defmacro(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::FnArity;

    if args.len() < 2 {
        return Err(Error::syntax("defmacro", "requires name, params, and body"));
    }

    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defmacro",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    // Skip optional docstring
    let rest = if matches!(&args[1], KlujurVal::String(_)) {
        &args[2..]
    } else {
        &args[1..]
    };

    if rest.is_empty() {
        return Err(Error::syntax("defmacro", "requires params and body"));
    }

    // Check if multi-arity (first form is a list) or single-arity (first form is a vector)
    let arities = if matches!(&rest[0], KlujurVal::List(_, _)) {
        // Multi-arity: (defmacro name ([x] ...) ([x y] ...))
        let mut arities = Vec::new();
        for arity_form in rest {
            let arity_list: Vec<KlujurVal> = match arity_form {
                KlujurVal::List(items, _) => items.iter().cloned().collect(),
                _ => {
                    return Err(Error::syntax(
                        "defmacro",
                        "each arity must be a list like ([params] body...)",
                    ));
                }
            };
            if arity_list.is_empty() {
                return Err(Error::syntax(
                    "defmacro",
                    "arity requires a parameter vector",
                ));
            }
            let (params, rest_param, patterns, rest_pattern, body) =
                parse_fn_arity(&arity_list[0], &arity_list[1..])?;
            arities.push(FnArity::with_patterns(
                params,
                rest_param,
                patterns,
                rest_pattern,
                body,
            ));
        }
        arities
    } else {
        // Single-arity: (defmacro name [params] body...)
        let (params, rest_param, patterns, rest_pattern, body) =
            parse_fn_arity(&rest[0], &rest[1..])?;

        if body.is_empty() {
            return Err(Error::syntax("defmacro", "requires a body"));
        }
        vec![FnArity::with_patterns(
            params,
            rest_param,
            patterns,
            rest_pattern,
            body,
        )]
    };

    // Create the macro (reuse KlujurFn structure)
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let macro_fn = KlujurFn::new_multi(Some(name.clone()), arities, env_any);

    let macro_val = KlujurVal::Macro(macro_fn);

    // Define in namespace like def does
    let registry = env.registry();
    let current_ns = registry.current();
    let var = current_ns.intern_with_value(name.name(), macro_val);

    Ok(KlujurVal::Var(var))
}

/// (macroexpand-1 form) - expand a macro form once
fn eval_macroexpand_1(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax(
            "macroexpand-1",
            "requires exactly 1 argument",
        ));
    }

    // Evaluate the argument to get the form (usually quoted)
    let form = eval(&args[0], env)?;
    macroexpand_1(&form, env)
}

/// Perform a single macro expansion
fn macroexpand_1(form: &KlujurVal, env: &Env) -> Result<KlujurVal> {
    // Only list forms can be macro calls
    let items: Vec<KlujurVal> = match form {
        KlujurVal::List(items, _) if !items.is_empty() => items.iter().cloned().collect(),
        _ => return Ok(form.clone()),
    };

    // Try to resolve the first element to a macro
    let op = match eval(&items[0], env) {
        Ok(val) => val,
        Err(_) => return Ok(form.clone()), // If can't resolve, not a macro
    };

    // If it's a macro, expand it
    if let KlujurVal::Macro(m) = &op {
        apply_fn(m, &items[1..])
    } else {
        Ok(form.clone())
    }
}

/// (macroexpand form) - fully expand a macro form
fn eval_macroexpand(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("macroexpand", "requires exactly 1 argument"));
    }

    // Evaluate the argument to get the form (usually quoted)
    let form = eval(&args[0], env)?;
    macroexpand(&form, env)
}

/// Fully expand all macros in a form
fn macroexpand(form: &KlujurVal, env: &Env) -> Result<KlujurVal> {
    let mut current = form.clone();
    loop {
        let expanded = macroexpand_1(&current, env)?;
        if expanded == current {
            return Ok(current);
        }
        current = expanded;
    }
}

// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use klujur_parser::{Keyword, Parser, Symbol};

    fn eval_str(s: &str) -> Result<KlujurVal> {
        let mut parser = Parser::new(s).expect("parser creation failed");
        let expr = parser.parse().expect("parse error").expect("empty input");
        let env = Env::new();
        eval(&expr, &env)
    }

    fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal> {
        let mut parser = Parser::new(s).expect("parser creation failed");
        let expr = parser.parse().expect("parse error").expect("empty input");
        eval(&expr, env)
    }

    #[test]
    fn test_self_evaluating() {
        assert_eq!(eval_str("42").unwrap(), KlujurVal::int(42));
        assert_eq!(eval_str("3.14").unwrap(), KlujurVal::float(3.14));
        assert_eq!(eval_str("true").unwrap(), KlujurVal::bool(true));
        assert_eq!(eval_str("false").unwrap(), KlujurVal::bool(false));
        assert_eq!(eval_str("nil").unwrap(), KlujurVal::Nil);
        assert_eq!(eval_str("\"hello\"").unwrap(), KlujurVal::string("hello"));
        assert_eq!(eval_str("\\a").unwrap(), KlujurVal::char('a'));
        assert_eq!(
            eval_str(":foo").unwrap(),
            KlujurVal::keyword(Keyword::new("foo"))
        );
    }

    #[test]
    fn test_quote() {
        assert_eq!(
            eval_str("(quote x)").unwrap(),
            KlujurVal::symbol(Symbol::new("x"))
        );
        assert_eq!(eval_str("'x").unwrap(), KlujurVal::symbol(Symbol::new("x")));
        assert_eq!(
            eval_str("'(1 2 3)").unwrap(),
            KlujurVal::list(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3)
            ])
        );
    }

    #[test]
    fn test_if() {
        assert_eq!(eval_str("(if true 1 2)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(if false 1 2)").unwrap(), KlujurVal::int(2));
        assert_eq!(eval_str("(if nil 1 2)").unwrap(), KlujurVal::int(2));
        assert_eq!(eval_str("(if 0 1 2)").unwrap(), KlujurVal::int(1)); // 0 is truthy
        assert_eq!(eval_str("(if false 1)").unwrap(), KlujurVal::Nil);
    }

    #[test]
    fn test_do() {
        assert_eq!(eval_str("(do)").unwrap(), KlujurVal::Nil);
        assert_eq!(eval_str("(do 1)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(do 1 2 3)").unwrap(), KlujurVal::int(3));
    }

    #[test]
    fn test_let() {
        assert_eq!(eval_str("(let* [x 1] x)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(let* [x 1 y 2] y)").unwrap(), KlujurVal::int(2));
        // Sequential binding
        assert_eq!(eval_str("(let* [x 1 y x] y)").unwrap(), KlujurVal::int(1));
    }

    #[test]
    fn test_def() {
        let env = Env::new();
        eval_str_with_env("(def x 42)", &env).unwrap();
        assert_eq!(eval_str_with_env("x", &env).unwrap(), KlujurVal::int(42));
    }

    #[test]
    fn test_fn_basic() {
        let env = Env::new();
        eval_str_with_env("(def add1 (fn* [x] x))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(add1 42)", &env).unwrap(),
            KlujurVal::int(42)
        );
    }

    #[test]
    fn test_fn_closure() {
        let env = Env::new();
        eval_str_with_env("(def x 10)", &env).unwrap();
        eval_str_with_env("(def get-x (fn* [] x))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(get-x)", &env).unwrap(),
            KlujurVal::int(10)
        );
    }

    #[test]
    fn test_fn_rest_args() {
        let env = Env::new();
        eval_str_with_env("(def rest-fn (fn* [& args] args))", &env).unwrap();
        let result = eval_str_with_env("(rest-fn 1 2 3)", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3)
            ])
        );
    }

    #[test]
    fn test_keyword_as_function() {
        let env = Env::new();
        eval_str_with_env("(def m {:a 1 :b 2})", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(:a m)", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(eval_str_with_env("(:c m)", &env).unwrap(), KlujurVal::Nil);
        assert_eq!(
            eval_str_with_env("(:c m 99)", &env).unwrap(),
            KlujurVal::int(99)
        );
    }

    #[test]
    fn test_vector_eval() {
        let env = Env::new();
        eval_str_with_env("(def x 1)", &env).unwrap();
        assert_eq!(
            eval_str_with_env("[x 2 3]", &env).unwrap(),
            KlujurVal::vector(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3)
            ])
        );
    }

    #[test]
    fn test_builtins_arithmetic() {
        use crate::builtins::register_builtins;

        let env = Env::new();
        register_builtins(&env);

        assert_eq!(
            eval_str_with_env("(+ 1 2 3)", &env).unwrap(),
            KlujurVal::int(6)
        );
        assert_eq!(
            eval_str_with_env("(- 10 3)", &env).unwrap(),
            KlujurVal::int(7)
        );
        assert_eq!(
            eval_str_with_env("(* 2 3 4)", &env).unwrap(),
            KlujurVal::int(24)
        );
        assert_eq!(
            eval_str_with_env("(/ 10 2)", &env).unwrap(),
            KlujurVal::float(5.0)
        );
    }

    #[test]
    fn test_builtins_comparison() {
        use crate::builtins::register_builtins;

        let env = Env::new();
        register_builtins(&env);

        assert_eq!(
            eval_str_with_env("(= 1 1)", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(< 1 2)", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(> 2 1)", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(not= 1 2)", &env).unwrap(),
            KlujurVal::bool(true)
        );
    }

    #[test]
    fn test_builtins_predicates() {
        use crate::builtins::register_builtins;

        let env = Env::new();
        register_builtins(&env);

        assert_eq!(
            eval_str_with_env("(nil? nil)", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(number? 42)", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(string? \"hello\")", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(list? '(1 2 3))", &env).unwrap(),
            KlujurVal::bool(true)
        );
    }

    #[test]
    fn test_builtins_sequences() {
        use crate::builtins::register_builtins;

        let env = Env::new();
        register_builtins(&env);

        assert_eq!(
            eval_str_with_env("(first '(1 2 3))", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(
            eval_str_with_env("(count '(1 2 3))", &env).unwrap(),
            KlujurVal::int(3)
        );
        assert_eq!(
            eval_str_with_env("(nth [10 20 30] 1)", &env).unwrap(),
            KlujurVal::int(20)
        );
    }

    #[test]
    fn test_fn_with_builtins() {
        use crate::builtins::register_builtins;

        let env = Env::new();
        register_builtins(&env);

        eval_str_with_env("(def add (fn* [a b] (+ a b)))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(add 3 4)", &env).unwrap(),
            KlujurVal::int(7)
        );

        eval_str_with_env(
            "(def factorial (fn* [n] (if (<= n 1) 1 (* n (factorial (- n 1))))))",
            &env,
        )
        .unwrap();
        assert_eq!(
            eval_str_with_env("(factorial 5)", &env).unwrap(),
            KlujurVal::int(120)
        );
    }

    #[test]
    fn test_loop_basic() {
        assert_eq!(eval_str("(loop [x 1] x)").unwrap(), KlujurVal::int(1));
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        assert_eq!(
            eval_str_with_env("(loop [x 1 y 2] (+ x y))", &env).unwrap(),
            KlujurVal::int(3)
        );
    }

    #[test]
    fn test_loop_recur() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Count up to 10
        assert_eq!(
            eval_str_with_env("(loop [x 0] (if (< x 10) (recur (+ x 1)) x))", &env).unwrap(),
            KlujurVal::int(10)
        );
    }

    #[test]
    fn test_loop_recur_sum() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Sum 1 to 10 = 55
        let result = eval_str_with_env(
            "(loop [n 10 acc 0] (if (= n 0) acc (recur (- n 1) (+ acc n))))",
            &env,
        )
        .unwrap();
        assert_eq!(result, KlujurVal::int(55));
    }

    #[test]
    fn test_loop_recur_factorial() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // factorial(5) = 120
        let result = eval_str_with_env(
            "(loop [n 5 acc 1] (if (= n 0) acc (recur (- n 1) (* acc n))))",
            &env,
        )
        .unwrap();
        assert_eq!(result, KlujurVal::int(120));
    }

    #[test]
    fn test_recur_arity_error() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Too few arguments to recur
        let result = eval_str_with_env("(loop [x 1 y 2] (recur 3))", &env);
        assert!(result.is_err());
    }

    #[test]
    fn test_apply_basic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Apply + to a list
        assert_eq!(
            eval_str_with_env("(apply + [1 2 3])", &env).unwrap(),
            KlujurVal::int(6)
        );
    }

    #[test]
    fn test_apply_with_intermediate_args() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Apply with intermediate args
        assert_eq!(
            eval_str_with_env("(apply + 1 2 [3 4])", &env).unwrap(),
            KlujurVal::int(10)
        );
    }

    #[test]
    fn test_apply_user_fn() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def add3 (fn* [a b c] (+ a b c)))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(apply add3 [1 2 3])", &env).unwrap(),
            KlujurVal::int(6)
        );
    }

    #[test]
    fn test_apply_empty_seq() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Apply + to empty list
        assert_eq!(
            eval_str_with_env("(apply + [])", &env).unwrap(),
            KlujurVal::int(0)
        );
    }

    #[test]
    fn test_apply_nil() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // nil treated as empty seq
        assert_eq!(
            eval_str_with_env("(apply + 1 2 nil)", &env).unwrap(),
            KlujurVal::int(3)
        );
    }

    #[test]
    fn test_map_basic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def inc (fn* [x] (+ x 1)))", &env).unwrap();
        // Use map* builtin directly (map is in stdlib with transducer support)
        let result = eval_str_with_env("(map* inc [1 2 3])", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::int(2),
                KlujurVal::int(3),
                KlujurVal::int(4)
            ])
        );
    }

    #[test]
    fn test_filter_basic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def positive? (fn* [x] (> x 0)))", &env).unwrap();
        // Use filter* builtin directly (filter is in stdlib with transducer support)
        let result = eval_str_with_env("(filter* positive? [-1 0 1 2 -3 4])", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(4)
            ])
        );
    }

    #[test]
    fn test_reduce_basic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Sum of 1 to 5 = 15
        assert_eq!(
            eval_str_with_env("(reduce + [1 2 3 4 5])", &env).unwrap(),
            KlujurVal::int(15)
        );
    }

    #[test]
    fn test_reduce_with_init() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Sum with initial value
        assert_eq!(
            eval_str_with_env("(reduce + 10 [1 2 3])", &env).unwrap(),
            KlujurVal::int(16)
        );
    }

    #[test]
    fn test_every_some() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def positive? (fn* [x] (> x 0)))", &env).unwrap();

        assert_eq!(
            eval_str_with_env("(every? positive? [1 2 3])", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(every? positive? [1 -2 3])", &env).unwrap(),
            KlujurVal::bool(false)
        );
        assert_eq!(
            eval_str_with_env("(some positive? [-1 -2 3])", &env).unwrap(),
            KlujurVal::bool(true)
        );
    }

    #[test]
    fn test_partial() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def add5 (partial + 5))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(add5 10)", &env).unwrap(),
            KlujurVal::int(15)
        );
    }

    #[test]
    fn test_constantly() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        eval_str_with_env("(def always42 (constantly 42))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(always42)", &env).unwrap(),
            KlujurVal::int(42)
        );
        assert_eq!(
            eval_str_with_env("(always42 1 2 3)", &env).unwrap(),
            KlujurVal::int(42)
        );
    }

    #[test]
    fn test_and() {
        assert_eq!(eval_str("(and)").unwrap(), KlujurVal::bool(true));
        assert_eq!(eval_str("(and true)").unwrap(), KlujurVal::bool(true));
        assert_eq!(eval_str("(and true true)").unwrap(), KlujurVal::bool(true));
        assert_eq!(
            eval_str("(and true false)").unwrap(),
            KlujurVal::bool(false)
        );
        assert_eq!(
            eval_str("(and false true)").unwrap(),
            KlujurVal::bool(false)
        );
        // Returns last truthy value
        assert_eq!(eval_str("(and 1 2 3)").unwrap(), KlujurVal::int(3));
    }

    #[test]
    fn test_or() {
        assert_eq!(eval_str("(or)").unwrap(), KlujurVal::Nil);
        assert_eq!(eval_str("(or true)").unwrap(), KlujurVal::bool(true));
        assert_eq!(eval_str("(or false true)").unwrap(), KlujurVal::bool(true));
        assert_eq!(
            eval_str("(or false false)").unwrap(),
            KlujurVal::bool(false)
        );
        // Returns first truthy value
        assert_eq!(eval_str("(or nil 2 3)").unwrap(), KlujurVal::int(2));
    }

    #[test]
    fn test_when() {
        assert_eq!(eval_str("(when true 1)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(when false 1)").unwrap(), KlujurVal::Nil);
        assert_eq!(eval_str("(when true 1 2 3)").unwrap(), KlujurVal::int(3));
    }

    #[test]
    fn test_when_not() {
        assert_eq!(eval_str("(when-not false 1)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(when-not true 1)").unwrap(), KlujurVal::Nil);
        assert_eq!(eval_str("(when-not nil 1 2 3)").unwrap(), KlujurVal::int(3));
    }

    #[test]
    fn test_if_not() {
        assert_eq!(eval_str("(if-not true 1 2)").unwrap(), KlujurVal::int(2));
        assert_eq!(eval_str("(if-not false 1 2)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(if-not nil 1 2)").unwrap(), KlujurVal::int(1));
        assert_eq!(eval_str("(if-not true 1)").unwrap(), KlujurVal::Nil);
    }

    #[test]
    fn test_cond() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        assert_eq!(
            eval_str_with_env("(cond true 1)", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(
            eval_str_with_env("(cond false 1 true 2)", &env).unwrap(),
            KlujurVal::int(2)
        );
        assert_eq!(
            eval_str_with_env("(cond false 1 false 2)", &env).unwrap(),
            KlujurVal::Nil
        );
        // :else clause
        assert_eq!(
            eval_str_with_env("(cond false 1 :else 2)", &env).unwrap(),
            KlujurVal::int(2)
        );
    }

    #[test]
    fn test_multi_arity_fn() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Multi-arity function
        eval_str_with_env(
            "(def foo (fn* ([x] x) ([x y] (+ x y)) ([x y z] (+ x y z))))",
            &env,
        )
        .unwrap();

        assert_eq!(
            eval_str_with_env("(foo 1)", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(
            eval_str_with_env("(foo 1 2)", &env).unwrap(),
            KlujurVal::int(3)
        );
        assert_eq!(
            eval_str_with_env("(foo 1 2 3)", &env).unwrap(),
            KlujurVal::int(6)
        );
    }

    #[test]
    fn test_multi_arity_with_rest() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Multi-arity with rest parameter in one arity
        eval_str_with_env(
            "(def bar (fn* ([x] x) ([x y & more] (+ x y (apply + more)))))",
            &env,
        )
        .unwrap();

        assert_eq!(
            eval_str_with_env("(bar 5)", &env).unwrap(),
            KlujurVal::int(5)
        );
        assert_eq!(
            eval_str_with_env("(bar 1 2)", &env).unwrap(),
            KlujurVal::int(3)
        );
        assert_eq!(
            eval_str_with_env("(bar 1 2 3 4)", &env).unwrap(),
            KlujurVal::int(10)
        );
    }

    #[test]
    fn test_multi_arity_error() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Should error with wrong arity
        eval_str_with_env("(def baz (fn* ([x] x) ([x y] (+ x y))))", &env).unwrap();

        let result = eval_str_with_env("(baz 1 2 3)", &env);
        assert!(result.is_err());
    }

    #[test]
    fn test_thread_first() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // (-> 1 (+ 2)) => (+ 1 2) => 3
        assert_eq!(
            eval_str_with_env("(-> 1 (+ 2))", &env).unwrap(),
            KlujurVal::int(3)
        );
        // (-> 5 (- 2) (- 1)) => (- (- 5 2) 1) => (- 3 1) => 2
        assert_eq!(
            eval_str_with_env("(-> 5 (- 2) (- 1))", &env).unwrap(),
            KlujurVal::int(2)
        );
        // with symbol (inc is not defined, so use fn)
        eval_str_with_env("(def inc2 (fn* [x] (+ x 2)))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(-> 1 inc2)", &env).unwrap(),
            KlujurVal::int(3)
        );
    }

    #[test]
    fn test_thread_last() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // (->> [1 2 3] (map* inc)) => (map* inc [1 2 3])
        // Use map* builtin directly (map is in stdlib with transducer support)
        eval_str_with_env("(def incfn (fn* [x] (+ x 1)))", &env).unwrap();
        let result = eval_str_with_env("(->> [1 2 3] (map* incfn))", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::int(2),
                KlujurVal::int(3),
                KlujurVal::int(4)
            ])
        );
    }

    #[test]
    fn test_as_thread() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // (as-> 1 x (+ x x)) => 2
        assert_eq!(
            eval_str_with_env("(as-> 1 x (+ x x))", &env).unwrap(),
            KlujurVal::int(2)
        );
        // Can use x in any position
        assert_eq!(
            eval_str_with_env("(as-> 5 v (- 10 v))", &env).unwrap(),
            KlujurVal::int(5)
        );
    }

    #[test]
    fn test_in_ns() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Switch to a new namespace
        let result = eval_str_with_env("(in-ns 'test.core)", &env).unwrap();
        assert_eq!(result, KlujurVal::symbol(Symbol::new("test.core")));

        // Define something in the new namespace
        eval_str_with_env("(def x 42)", &env).unwrap();
        assert_eq!(eval_str_with_env("x", &env).unwrap(), KlujurVal::int(42));
    }

    #[test]
    fn test_var_special_form() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Define a var
        eval_str_with_env("(def x 42)", &env).unwrap();

        // Get the var itself
        let result = eval_str_with_env("(var x)", &env).unwrap();
        assert!(matches!(result, KlujurVal::Var(_)));

        // var? predicate
        assert_eq!(
            eval_str_with_env("(var? (var x))", &env).unwrap(),
            KlujurVal::bool(true)
        );
        assert_eq!(
            eval_str_with_env("(var? x)", &env).unwrap(),
            KlujurVal::bool(false)
        );
    }

    #[test]
    fn test_deref() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Define a var
        eval_str_with_env("(def x 42)", &env).unwrap();

        // Deref the var to get the value
        assert_eq!(
            eval_str_with_env("(deref (var x))", &env).unwrap(),
            KlujurVal::int(42)
        );
    }

    #[test]
    fn test_def_returns_var() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // def should return a Var
        let result = eval_str_with_env("(def x 42)", &env).unwrap();
        assert!(matches!(result, KlujurVal::Var(_)));
    }

    #[test]
    fn test_defmacro_basic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Simple identity macro
        eval_str_with_env("(defmacro identity [x] x)", &env).unwrap();
        // Using it should return the unevaluated arg
        assert_eq!(
            eval_str_with_env("(identity 42)", &env).unwrap(),
            KlujurVal::int(42)
        );
    }

    #[test]
    fn test_defmacro_list_construction() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Macro that builds a list
        eval_str_with_env("(defmacro my-list [a b] (list 'list a b))", &env).unwrap();
        let result = eval_str_with_env("(my-list 1 2)", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![KlujurVal::int(1), KlujurVal::int(2)])
        );
    }

    #[test]
    fn test_macroexpand_1() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Define a simple macro
        eval_str_with_env("(defmacro double [x] (list '+ x x))", &env).unwrap();
        // Expand it once
        let result = eval_str_with_env("(macroexpand-1 '(double 5))", &env).unwrap();
        // Should expand to (+ 5 5)
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::symbol(Symbol::new("+")),
                KlujurVal::int(5),
                KlujurVal::int(5)
            ])
        );
    }

    #[test]
    fn test_macro_evaluation() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Macro that doubles a number by constructing (+ x x)
        eval_str_with_env("(defmacro double [x] (list '+ x x))", &env).unwrap();
        // Using the macro should evaluate to the doubled value
        assert_eq!(
            eval_str_with_env("(double 5)", &env).unwrap(),
            KlujurVal::int(10)
        );
    }

    #[test]
    fn test_macro_does_not_eval_args() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Macro that returns its argument as a quoted form
        eval_str_with_env("(defmacro quote-form [form] (list 'quote form))", &env).unwrap();
        // The form (+ 1 2) should not be evaluated
        let result = eval_str_with_env("(quote-form (+ 1 2))", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::symbol(Symbol::new("+")),
                KlujurVal::int(1),
                KlujurVal::int(2)
            ])
        );
    }

    // ========================================================================
    // Destructuring Tests
    // ========================================================================

    #[test]
    fn test_let_sequential_destructure() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Basic sequential destructuring
        assert_eq!(
            eval_str_with_env("(let* [[a b c] [1 2 3]] a)", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(
            eval_str_with_env("(let* [[a b c] [1 2 3]] b)", &env).unwrap(),
            KlujurVal::int(2)
        );
        assert_eq!(
            eval_str_with_env("(let* [[a b c] [1 2 3]] c)", &env).unwrap(),
            KlujurVal::int(3)
        );
    }

    #[test]
    fn test_let_sequential_destructure_rest() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Rest destructuring with &
        let result = eval_str_with_env("(let* [[a & rest] [1 2 3 4]] rest)", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::list(vec![
                KlujurVal::int(2),
                KlujurVal::int(3),
                KlujurVal::int(4)
            ])
        );
    }

    #[test]
    fn test_let_sequential_destructure_as() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // :as binding for entire collection
        let result = eval_str_with_env("(let* [[a b :as all] [1 2 3]] all)", &env).unwrap();
        assert_eq!(
            result,
            KlujurVal::vector(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3)
            ])
        );
    }

    #[test]
    fn test_let_sequential_destructure_ignore() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // _ ignores a position
        assert_eq!(
            eval_str_with_env("(let* [[_ b _] [1 2 3]] b)", &env).unwrap(),
            KlujurVal::int(2)
        );
    }

    #[test]
    fn test_let_sequential_destructure_nested() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Nested sequential destructuring
        assert_eq!(
            eval_str_with_env("(let* [[a [b c]] [1 [2 3]]] c)", &env).unwrap(),
            KlujurVal::int(3)
        );
    }

    #[test]
    fn test_let_map_destructure_keys() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // :keys destructuring
        assert_eq!(
            eval_str_with_env("(let* [{:keys [a b]} {:a 1 :b 2}] a)", &env).unwrap(),
            KlujurVal::int(1)
        );
        assert_eq!(
            eval_str_with_env("(let* [{:keys [a b]} {:a 1 :b 2}] b)", &env).unwrap(),
            KlujurVal::int(2)
        );
    }

    #[test]
    fn test_let_map_destructure_as() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // :as binding for entire map
        let result = eval_str_with_env("(let* [{:keys [a] :as m} {:a 1 :b 2}] m)", &env).unwrap();
        if let KlujurVal::Map(map, _) = result {
            assert_eq!(map.len(), 2);
        } else {
            panic!("Expected a map");
        }
    }

    #[test]
    fn test_let_map_destructure_or_defaults() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // :or provides defaults for missing keys
        assert_eq!(
            eval_str_with_env("(let* [{:keys [a b] :or {b 99}} {:a 1}] b)", &env).unwrap(),
            KlujurVal::int(99)
        );
        // Present value overrides default
        assert_eq!(
            eval_str_with_env("(let* [{:keys [a b] :or {b 99}} {:a 1 :b 2}] b)", &env).unwrap(),
            KlujurVal::int(2)
        );
    }

    #[test]
    fn test_fn_sequential_destructure() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Function with destructuring parameter
        eval_str_with_env("(def first-two (fn* [[a b]] (+ a b)))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(first-two [3 4])", &env).unwrap(),
            KlujurVal::int(7)
        );
    }

    #[test]
    fn test_fn_map_destructure() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Function with map destructuring
        eval_str_with_env("(def get-a (fn* [{:keys [a]}] a))", &env).unwrap();
        assert_eq!(
            eval_str_with_env("(get-a {:a 42 :b 99})", &env).unwrap(),
            KlujurVal::int(42)
        );
    }

    #[test]
    fn test_loop_sequential_destructure() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Loop with destructuring
        let result = eval_str_with_env(
            "(loop [[x & rest] [1 2 3] acc 0]
               (if (nil? rest)
                 (+ acc x)
                 (recur rest (+ acc x))))",
            &env,
        )
        .unwrap();
        // 1 + 2 + 3 = 6
        assert_eq!(result, KlujurVal::int(6));
    }

    #[test]
    fn test_destructure_nil_value() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Destructuring nil gives nil for all bindings
        assert_eq!(
            eval_str_with_env("(let* [[a b] nil] a)", &env).unwrap(),
            KlujurVal::Nil
        );
    }

    #[test]
    fn test_destructure_short_collection() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);
        // Missing elements become nil
        assert_eq!(
            eval_str_with_env("(let* [[a b c] [1 2]] c)", &env).unwrap(),
            KlujurVal::Nil
        );
    }

    #[test]
    fn test_private_var_qualified_access_denied() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Create a namespace with a private var using ^:private syntax
        eval_str_with_env("(in-ns 'test.priv)", &env).unwrap();
        eval_str_with_env("(def ^:private secret 42)", &env).unwrap();

        // Switch to user namespace
        eval_str_with_env("(in-ns 'user)", &env).unwrap();

        // Accessing the private var should fail
        let result = eval_str_with_env("test.priv/secret", &env);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not public"));
    }

    #[test]
    fn test_public_var_qualified_access_allowed() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Create a namespace with a public var
        eval_str_with_env("(in-ns 'test.pub)", &env).unwrap();
        eval_str_with_env("(def public-val 42)", &env).unwrap();

        // Switch to user namespace
        eval_str_with_env("(in-ns 'user)", &env).unwrap();

        // Accessing the public var should work
        let result = eval_str_with_env("test.pub/public-val", &env).unwrap();
        assert_eq!(result, KlujurVal::int(42));
    }

    #[test]
    fn test_private_var_same_ns_access_allowed() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Create a namespace with a private var using ^:private syntax
        eval_str_with_env("(in-ns 'test.same)", &env).unwrap();
        eval_str_with_env("(def ^:private secret 42)", &env).unwrap();

        // Access from same namespace via qualified name should work
        let result = eval_str_with_env("test.same/secret", &env).unwrap();
        assert_eq!(result, KlujurVal::int(42));
    }

    #[test]
    fn test_ns_publics() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Create a namespace with public and private vars using ^:private syntax
        eval_str_with_env("(in-ns 'test.nspub)", &env).unwrap();
        eval_str_with_env("(def public-var 1)", &env).unwrap();
        eval_str_with_env("(def ^:private private-var 2)", &env).unwrap();
        eval_str_with_env("(in-ns 'user)", &env).unwrap();

        // ns-publics should include public, exclude private
        let result =
            eval_str_with_env("(contains? (ns-publics 'test.nspub) 'public-var)", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));

        let result =
            eval_str_with_env("(contains? (ns-publics 'test.nspub) 'private-var)", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(false));
    }

    #[test]
    fn test_ns_interns() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Create a namespace with public and private vars using ^:private syntax
        eval_str_with_env("(in-ns 'test.nsint)", &env).unwrap();
        eval_str_with_env("(def public-var 1)", &env).unwrap();
        eval_str_with_env("(def ^:private private-var 2)", &env).unwrap();
        eval_str_with_env("(in-ns 'user)", &env).unwrap();

        // ns-interns should include both
        let result =
            eval_str_with_env("(contains? (ns-interns 'test.nsint) 'public-var)", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));

        let result =
            eval_str_with_env("(contains? (ns-interns 'test.nsint) 'private-var)", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));
    }

    #[test]
    fn test_def_with_meta_keyword() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Test that ^:private metadata is applied to the var
        eval_str_with_env("(def ^:private secret 42)", &env).unwrap();

        // Get the var and check its metadata
        let result = eval_str_with_env("(:private (meta #'secret))", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));

        // Value should still be accessible
        let result = eval_str_with_env("secret", &env).unwrap();
        assert_eq!(result, KlujurVal::int(42));
    }

    #[test]
    fn test_def_with_meta_dynamic() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Test ^:dynamic metadata
        eval_str_with_env("(def ^:dynamic *x* 1)", &env).unwrap();

        let result = eval_str_with_env("(:dynamic (meta #'*x*))", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));
    }

    #[test]
    fn test_def_with_meta_stacked() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Test stacked metadata: ^:private ^:dynamic
        eval_str_with_env("(def ^:private ^:dynamic *secret* 100)", &env).unwrap();

        let result = eval_str_with_env("(:private (meta #'*secret*))", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));

        let result = eval_str_with_env("(:dynamic (meta #'*secret*))", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));
    }

    #[test]
    fn test_def_with_meta_map() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Test full map metadata
        eval_str_with_env(
            r#"(def ^{:doc "A test var" :private true} documented 1)"#,
            &env,
        )
        .unwrap();

        let result = eval_str_with_env("(:doc (meta #'documented))", &env).unwrap();
        if let KlujurVal::String(s) = result {
            assert_eq!(s.as_ref(), "A test var");
        } else {
            panic!("Expected string");
        }

        let result = eval_str_with_env("(:private (meta #'documented))", &env).unwrap();
        assert_eq!(result, KlujurVal::bool(true));
    }

    // =========================================================================
    // Bytecode mode tests
    // =========================================================================

    #[test]
    fn test_bytecode_mode_simple_function() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Enable bytecode mode
        let prev = set_bytecode_mode(true);

        // Create a simple function
        let result = eval_str_with_env("((fn [x] x) 42)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(42));

        // Restore previous mode
        let _ = set_bytecode_mode(prev);
    }

    #[test]
    fn test_bytecode_mode_literal_return() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        let prev = set_bytecode_mode(true);

        // Function returning a literal
        let result = eval_str_with_env("((fn [] 123))", &env).unwrap();
        assert_eq!(result, KlujurVal::int(123));

        let _ = set_bytecode_mode(prev);
    }

    #[test]
    fn test_bytecode_mode_if_expr() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        let prev = set_bytecode_mode(true);

        // Function with if expression
        let result = eval_str_with_env("((fn [x] (if x 1 0)) true)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(1));

        let result = eval_str_with_env("((fn [x] (if x 1 0)) false)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(0));

        let _ = set_bytecode_mode(prev);
    }

    #[test]
    fn test_bytecode_mode_named_function() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        let prev = set_bytecode_mode(true);

        // Named function
        let result = eval_str_with_env("((fn my-fn [x] x) 99)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(99));

        let _ = set_bytecode_mode(prev);
    }

    #[test]
    fn test_bytecode_mode_disabled_uses_interpreter() {
        let env = Env::new();
        crate::builtins::register_builtins(&env);

        // Make sure bytecode mode is disabled
        let _ = set_bytecode_mode(false);

        // Should use interpreter
        let result = eval_str_with_env("((fn [x] x) 42)", &env).unwrap();
        assert_eq!(result, KlujurVal::int(42));
    }
}
