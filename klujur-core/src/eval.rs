// klujur-core - AST-walking evaluator
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! AST-walking evaluator for Klujur expressions.

// Allow mutable key types - KlujurVal has interior mutability for Vars/Atoms by design
#![allow(clippy::mutable_key_type)]

use std::any::Any;
use std::rc::Rc;

use klujur_parser::{
    Keyword, KlujurFn, KlujurMultimethod, KlujurNativeFn, KlujurVal, KlujurVar, Meta, OrdMap,
    Symbol,
};

use crate::bindings::{deref_var, push_bindings, set_thread_binding};
use crate::env::Env;
use crate::error::{Error, Result};

/// Type alias for native function signature.
pub type NativeFnImpl = dyn Fn(&[KlujurVal]) -> Result<KlujurVal>;

/// Evaluate a Klujur expression in the given environment.
pub fn eval(expr: &KlujurVal, env: &Env) -> Result<KlujurVal> {
    match expr {
        // Self-evaluating forms
        KlujurVal::Nil
        | KlujurVal::Bool(_)
        | KlujurVal::Int(_)
        | KlujurVal::Float(_)
        | KlujurVal::Ratio(_, _)
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
        | KlujurVal::Record(_) => Ok(expr.clone()),

        // Symbol lookup - automatically dereferences Vars
        KlujurVal::Symbol(sym, _) => {
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
            "defmacro" => return eval_defmacro(&items[1..], env),
            "macroexpand-1" => return eval_macroexpand_1(&items[1..], env),
            "macroexpand" => return eval_macroexpand(&items[1..], env),
            "throw" => return eval_throw(&items[1..], env),
            "try" => return eval_try(&items[1..], env),
            "binding" => return eval_binding(&items[1..], env),
            "set!" => return eval_set_bang(&items[1..], env),
            "swap!" => return eval_swap(&items[1..], env),
            "swap-vals!" => return eval_swap_vals(&items[1..], env),
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
        return eval(&expanded, env);
    }

    // Regular function call - evaluate all forms then apply
    let mut evaluated = vec![op];
    for item in &items[1..] {
        evaluated.push(eval(item, env)?);
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
    if args.len() != 2 {
        return Err(Error::syntax("def", "requires exactly 2 arguments"));
    }

    // Extract symbol and metadata - handle both direct symbol and (with-meta sym meta)
    let (sym, sym_meta) = extract_symbol_and_meta(&args[0], env)?;

    let val = eval(&args[1], env)?;

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

    // Create function value with type-erased environment
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let func = KlujurFn::new_multi(fn_name, arities, env_any);
    Ok(KlujurVal::Fn(func))
}

/// Result of parsing fn* parameters: (params, rest_param, param_patterns, rest_pattern, body)
type ParsedFnArity = (
    Vec<Symbol>,
    Option<Symbol>,
    Vec<KlujurVal>,
    Option<KlujurVal>,
    Vec<KlujurVal>,
);

/// Parse a parameter vector and body for fn*
/// Supports destructuring patterns in parameter position.
fn parse_fn_arity(params_form: &KlujurVal, body_forms: &[KlujurVal]) -> Result<ParsedFnArity> {
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
    let mut binding_patterns: Vec<KlujurVal> = Vec::with_capacity(bindings.len() / 2);
    let mut binding_gensyms: Vec<Symbol> = Vec::with_capacity(bindings.len() / 2);
    let mut initial_values: Vec<KlujurVal> = Vec::with_capacity(bindings.len() / 2);

    for (i, pair) in bindings.chunks(2).enumerate() {
        let pattern = &pair[0];
        let val = eval(&pair[1], env)?;

        // Create a gensym for recur tracking (or use the symbol directly if simple)
        let gensym = match pattern {
            KlujurVal::Symbol(s, _) => s.clone(),
            _ => Symbol::new(&format!("__loop_{}", i)),
        };

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

/// (and exprs*) - short-circuit logical and
fn eval_and(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::bool(true));
    }

    let mut result = KlujurVal::bool(true);
    for expr in args {
        result = eval(expr, env)?;
        if !result.is_truthy() {
            return Ok(result);
        }
    }
    Ok(result)
}

/// (or exprs*) - short-circuit logical or
fn eval_or(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::Nil);
    }

    for expr in args {
        let result = eval(expr, env)?;
        if result.is_truthy() {
            return Ok(result);
        }
    }
    // Return the last falsy value
    eval(&args[args.len() - 1], env)
}

/// (when test body...) - execute body if test is truthy
fn eval_when(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("when", "requires at least a test expression"));
    }

    let test = eval(&args[0], env)?;
    if test.is_truthy() {
        let mut result = KlujurVal::Nil;
        for expr in &args[1..] {
            result = eval(expr, env)?;
        }
        Ok(result)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (when-not test body...) - execute body if test is falsy
fn eval_when_not(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax(
            "when-not",
            "requires at least a test expression",
        ));
    }

    let test = eval(&args[0], env)?;
    if !test.is_truthy() {
        let mut result = KlujurVal::Nil;
        for expr in &args[1..] {
            result = eval(expr, env)?;
        }
        Ok(result)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (if-not test then else?) - conditional with negated test
fn eval_if_not(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::syntax("if-not", "requires 2 or 3 arguments"));
    }

    let test = eval(&args[0], env)?;

    if !test.is_truthy() {
        eval(&args[1], env)
    } else if args.len() == 3 {
        eval(&args[2], env)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (cond clauses*) - multi-way conditional
fn eval_cond(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if !args.len().is_multiple_of(2) {
        return Err(Error::syntax("cond", "requires even number of forms"));
    }

    for pair in args.chunks(2) {
        let test = &pair[0];

        // Check for :else keyword
        let is_else = matches!(test, KlujurVal::Keyword(kw) if kw.name() == "else");

        let test_result = if is_else {
            KlujurVal::bool(true)
        } else {
            eval(test, env)?
        };

        if test_result.is_truthy() {
            return eval(&pair[1], env);
        }
    }

    Ok(KlujurVal::Nil)
}

/// (-> x forms...) - thread first: insert x as second item in each form
fn eval_thread_first(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("->", "requires at least one argument"));
    }

    let mut result = eval(&args[0], env)?;

    for form in &args[1..] {
        result = match form {
            KlujurVal::List(items, _) if !items.is_empty() => {
                // Insert result as second argument: (f a b) -> (f result a b)
                let mut new_list = vec![items[0].clone(), result];
                new_list.extend(items.iter().skip(1).cloned());
                eval(&KlujurVal::list(new_list), env)?
            }
            KlujurVal::Symbol(_, _) | KlujurVal::Keyword(_) => {
                // Symbol or keyword: treat as (f result)
                // Keywords can be used as functions to look up values in maps
                let call = KlujurVal::list(vec![form.clone(), result]);
                eval(&call, env)?
            }
            other => {
                return Err(Error::syntax(
                    "->",
                    format!(
                        "form must be a list, symbol, or keyword, got {}",
                        other.type_name()
                    ),
                ));
            }
        };
    }

    Ok(result)
}

/// (->> x forms...) - thread last: insert x as last item in each form
fn eval_thread_last(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("->>", "requires at least one argument"));
    }

    let mut result = eval(&args[0], env)?;

    for form in &args[1..] {
        result = match form {
            KlujurVal::List(items, _) if !items.is_empty() => {
                // Insert result as last argument: (f a b) -> (f a b result)
                let mut new_list: Vec<KlujurVal> = items.iter().cloned().collect();
                new_list.push(result);
                eval(&KlujurVal::list(new_list), env)?
            }
            KlujurVal::Symbol(_, _) | KlujurVal::Keyword(_) => {
                // Symbol or keyword: treat as (f result)
                // Keywords can be used as functions to look up values in maps
                let call = KlujurVal::list(vec![form.clone(), result]);
                eval(&call, env)?
            }
            other => {
                return Err(Error::syntax(
                    "->>",
                    format!(
                        "form must be a list, symbol, or keyword, got {}",
                        other.type_name()
                    ),
                ));
            }
        };
    }

    Ok(result)
}

/// (as-> expr name forms...) - thread with named binding
fn eval_as_thread(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::syntax(
            "as->",
            "requires expression, name, and forms",
        ));
    }

    let name = match &args[1] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "as->",
                format!(
                    "second argument must be a symbol, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let mut result = eval(&args[0], env)?;

    // Create a child environment for the binding
    let thread_env = env.child();

    for form in &args[2..] {
        thread_env.define(name.clone(), result);
        result = eval(form, &thread_env)?;
    }

    Ok(result)
}

/// (in-ns 'name) - change current namespace
fn eval_in_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("in-ns", "requires exactly 1 argument"));
    }

    // in-ns evaluates its argument (unlike ns which is typically a macro)
    let arg = eval(&args[0], env)?;

    let name = match arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::syntax(
                "in-ns",
                format!(
                    "argument must be a symbol or string, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let registry = env.registry();
    let ns = registry.set_current(name);

    // Return the namespace name as a symbol
    Ok(KlujurVal::symbol(Symbol::new(&ns.name())))
}

/// (var sym) - get the Var itself (not its value)
fn eval_var(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("var", "requires exactly 1 argument"));
    }

    let sym = match &args[0] {
        KlujurVal::Symbol(s, _) => s,
        other => {
            return Err(Error::syntax(
                "var",
                format!("argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    // Look up the symbol (check both lexical env and namespace)
    let val = lookup_symbol(sym, env)?;

    // Return the Var if it is one, otherwise error
    match val {
        KlujurVal::Var(_) => Ok(val),
        _ => Err(Error::syntax(
            "var",
            format!("symbol '{}' is not bound to a Var", sym),
        )),
    }
}

/// Helper to get a namespace from an evaluated argument (symbol or string).
fn get_namespace_from_arg(
    arg: &KlujurVal,
    env: &Env,
    fn_name: &str,
) -> Result<crate::namespace::Namespace> {
    let ns_name = match arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::EvalError(format!(
                "{}: argument must be a symbol or string, got {}",
                fn_name,
                other.type_name()
            )));
        }
    };

    let registry = env.registry();
    registry
        .find(&ns_name)
        .ok_or_else(|| Error::EvalError(format!("No namespace: {}", ns_name)))
}

/// (ns-publics ns) - returns a map of symbols to public vars in namespace
fn eval_ns_publics(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-publics", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns = get_namespace_from_arg(&arg, env, "ns-publics")?;

    // Get public vars and convert to map of symbol -> var
    let publics = ns.publics();
    let pairs: Vec<(KlujurVal, KlujurVal)> = publics
        .into_iter()
        .map(|(name, var)| (KlujurVal::symbol(Symbol::new(&name)), KlujurVal::Var(var)))
        .collect();

    Ok(KlujurVal::map(pairs))
}

/// (ns-interns ns) - returns a map of symbols to all vars in namespace
fn eval_ns_interns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-interns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns = get_namespace_from_arg(&arg, env, "ns-interns")?;

    // Get all interned vars and convert to map of symbol -> var
    let interns = ns.interns();
    let pairs: Vec<(KlujurVal, KlujurVal)> = interns
        .into_iter()
        .map(|(name, var)| (KlujurVal::symbol(Symbol::new(&name)), KlujurVal::Var(var)))
        .collect();

    Ok(KlujurVal::map(pairs))
}

/// (refer ns-sym & filters) - refer vars from another namespace
///
/// Refers public vars from the specified namespace into the current namespace.
/// Private vars cannot be referred and will cause an error.
///
/// Basic usage: (refer 'other.ns)
/// With filters: (refer 'other.ns :only [foo bar])
///              (refer 'other.ns :exclude [baz])
///              (refer 'other.ns :rename {foo bar})
fn eval_refer(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("refer", "requires at least 1 argument"));
    }

    // Evaluate the namespace argument
    let ns_arg = eval(&args[0], env)?;
    let source_ns = get_namespace_from_arg(&ns_arg, env, "refer")?;

    let registry = env.registry();
    let current_ns = registry.current();

    // Parse filter options
    let mut only: Option<Vec<String>> = None;
    let mut exclude: Vec<String> = Vec::new();
    let mut rename: std::collections::HashMap<String, String> = std::collections::HashMap::new();

    let mut i = 1;
    while i < args.len() {
        let filter_key = eval(&args[i], env)?;
        match &filter_key {
            KlujurVal::Keyword(kw) if kw.name() == "only" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax("refer", ":only requires a vector argument"));
                }
                // Don't evaluate - use unevaluated symbols directly
                if let KlujurVal::Vector(items, _) = &args[i + 1] {
                    only = Some(
                        items
                            .iter()
                            .filter_map(|v| match v {
                                KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                _ => None,
                            })
                            .collect(),
                    );
                } else {
                    return Err(Error::syntax("refer", ":only requires a vector argument"));
                }
                i += 2;
            }
            KlujurVal::Keyword(kw) if kw.name() == "exclude" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax(
                        "refer",
                        ":exclude requires a vector argument",
                    ));
                }
                // Don't evaluate - use unevaluated symbols directly
                if let KlujurVal::Vector(items, _) = &args[i + 1] {
                    exclude = items
                        .iter()
                        .filter_map(|v| match v {
                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                            _ => None,
                        })
                        .collect();
                } else {
                    return Err(Error::syntax(
                        "refer",
                        ":exclude requires a vector argument",
                    ));
                }
                i += 2;
            }
            KlujurVal::Keyword(kw) if kw.name() == "rename" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax("refer", ":rename requires a map argument"));
                }
                // Don't evaluate - use unevaluated map directly
                if let KlujurVal::Map(map, _) = &args[i + 1] {
                    for (k, v) in map.iter() {
                        if let (KlujurVal::Symbol(ks, _), KlujurVal::Symbol(vs, _)) = (k, v) {
                            rename.insert(ks.name().to_string(), vs.name().to_string());
                        }
                    }
                } else {
                    return Err(Error::syntax("refer", ":rename requires a map argument"));
                }
                i += 2;
            }
            _ => {
                return Err(Error::syntax(
                    "refer",
                    format!("unknown filter option: {}", filter_key),
                ));
            }
        }
    }

    // Get public vars from source namespace
    let publics = source_ns.publics();

    // Determine which vars to refer
    let vars_to_refer: Vec<(String, _)> = match only {
        Some(only_list) => {
            // Only refer specified vars
            only_list
                .into_iter()
                .filter_map(|name| {
                    if exclude.contains(&name) {
                        return None;
                    }
                    if let Some(var) = publics.get(&name) {
                        let refer_name = rename.get(&name).cloned().unwrap_or(name);
                        Some((refer_name, var.clone()))
                    } else {
                        // Check if it exists but is private
                        if source_ns.interns().contains_key(&name) {
                            // Var exists but is private - this is an error
                            None // Will be handled below
                        } else {
                            None
                        }
                    }
                })
                .collect()
        }
        None => {
            // Refer all public vars
            publics
                .into_iter()
                .filter(|(name, _)| !exclude.contains(name))
                .map(|(name, var)| {
                    let refer_name = rename.get(&name).cloned().unwrap_or(name);
                    (refer_name, var)
                })
                .collect()
        }
    };

    // Check for private var access attempts in :only
    if let Some(ref only_list) = args.get(2).and_then(|_| {
        // Re-parse only list for error checking
        let mut i = 1;
        while i < args.len() {
            if let Ok(KlujurVal::Keyword(kw)) = eval(&args[i], env)
                && kw.name() == "only"
                && i + 1 < args.len()
                && let Ok(KlujurVal::Vector(items, _)) = eval(&args[i + 1], env)
            {
                return Some(
                    items
                        .iter()
                        .filter_map(|v| match v {
                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                );
            }
            i += 1;
        }
        None
    }) {
        let all_interns = source_ns.interns();
        let public_names: std::collections::HashSet<_> =
            source_ns.publics().keys().cloned().collect();

        for name in only_list {
            if all_interns.contains_key(name) && !public_names.contains(name) {
                return Err(Error::EvalError(format!("{} is not public", name)));
            }
        }
    }

    // Add refers to current namespace
    for (name, var) in vars_to_refer {
        current_ns.refer(name, var);
    }

    Ok(KlujurVal::Nil)
}

/// (alias alias-sym ns-sym) - Add an alias in the current namespace
///
/// Creates an alias so that `alias-sym/foo` resolves to `ns-sym/foo`.
/// Example: (alias 's 'clojure.string)
fn eval_alias(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::syntax("alias", "requires exactly 2 arguments"));
    }

    // Get alias symbol
    let alias_val = eval(&args[0], env)?;
    let alias_name = match &alias_val {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        other => {
            return Err(Error::type_error_in("alias", "symbol", other.type_name()));
        }
    };

    // Get target namespace symbol
    let ns_val = eval(&args[1], env)?;
    let ns_name = match &ns_val {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "alias",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();

    // Find or create the target namespace
    let target_ns = registry
        .find(&ns_name)
        .ok_or_else(|| Error::EvalError(format!("No namespace: {}", ns_name)))?;

    // Add alias to current namespace
    let current_ns = registry.current();
    current_ns.add_alias(alias_name, target_ns);

    Ok(KlujurVal::Nil)
}

/// Parse a require spec which can be:
/// - A symbol: 'mylib.utils
/// - A vector: '[mylib.utils :as u :refer [foo bar]]
fn parse_require_spec(spec: &KlujurVal) -> Result<(String, RequireOpts)> {
    match spec {
        KlujurVal::Symbol(s, _) => Ok((s.name().to_string(), RequireOpts::default())),
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                return Err(Error::syntax("require", "spec vector cannot be empty"));
            }

            // First element is the namespace name
            let ns_name = match &items[0] {
                KlujurVal::Symbol(s, _) => s.name().to_string(),
                other => {
                    return Err(Error::type_error_in("require", "symbol", other.type_name()));
                }
            };

            let mut opts = RequireOpts::default();
            let mut i = 1;

            while i < items.len() {
                match &items[i] {
                    KlujurVal::Keyword(kw) if kw.name() == "as" => {
                        if i + 1 >= items.len() {
                            return Err(Error::syntax("require", ":as requires a symbol"));
                        }
                        if let KlujurVal::Symbol(s, _) = &items[i + 1] {
                            opts.alias = Some(s.name().to_string());
                        } else {
                            return Err(Error::syntax("require", ":as requires a symbol"));
                        }
                        i += 2;
                    }
                    KlujurVal::Keyword(kw) if kw.name() == "refer" => {
                        if i + 1 >= items.len() {
                            return Err(Error::syntax(
                                "require",
                                ":refer requires a vector or :all",
                            ));
                        }
                        match &items[i + 1] {
                            KlujurVal::Vector(refs, _) => {
                                let names: Vec<String> = refs
                                    .iter()
                                    .filter_map(|v| match v {
                                        KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                        _ => None,
                                    })
                                    .collect();
                                opts.refer = Some(ReferSpec::Only(names));
                            }
                            KlujurVal::Keyword(kw) if kw.name() == "all" => {
                                opts.refer = Some(ReferSpec::All);
                            }
                            _ => {
                                return Err(Error::syntax(
                                    "require",
                                    ":refer requires a vector or :all",
                                ));
                            }
                        }
                        i += 2;
                    }
                    _ => {
                        i += 1;
                    }
                }
            }

            Ok((ns_name, opts))
        }
        other => Err(Error::type_error_in(
            "require",
            "symbol or vector",
            other.type_name(),
        )),
    }
}

#[derive(Default)]
struct RequireOpts {
    alias: Option<String>,
    refer: Option<ReferSpec>,
}

enum ReferSpec {
    All,
    Only(Vec<String>),
}

/// (require spec...) - Load and require namespaces
///
/// Supported forms:
/// - (require 'mylib.utils)
/// - (require '[mylib.utils :as u])
/// - (require '[mylib.utils :refer [foo bar]])
/// - (require '[mylib.utils :refer :all])
/// - (require 'ns1 'ns2 '[ns3 :as n])
///
/// Flags (can appear anywhere):
/// - :reload - reload namespace even if already loaded
/// - :reload-all - reload namespace and all its dependencies
fn eval_require(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("require", "requires at least 1 argument"));
    }

    let registry = env.registry();
    let mut reload = false;
    let mut reload_all = false;

    // First pass: check for :reload or :reload-all flags
    for arg in args {
        let val = eval(arg, env)?;
        if let KlujurVal::Keyword(kw) = &val {
            match kw.name() {
                "reload" => reload = true,
                "reload-all" => reload_all = true,
                _ => {}
            }
        }
    }

    // Save the original namespace before processing (files may switch namespaces)
    let original_ns_name = registry.current_name();

    // Process each require spec
    for arg in args {
        let val = eval(arg, env)?;

        // Skip flags
        if let KlujurVal::Keyword(kw) = &val
            && (kw.name() == "reload" || kw.name() == "reload-all")
        {
            continue;
        }

        let (ns_name, opts) = parse_require_spec(&val)?;

        // Check if we need to load
        let should_load = reload || reload_all || !registry.is_loaded(&ns_name);

        if should_load {
            // Mark for reload if requested
            if reload || reload_all {
                registry.reload(&ns_name);
            }

            // Find the file
            if let Some(path) = registry.find_namespace_file(&ns_name) {
                // Load the file
                let content = std::fs::read_to_string(&path).map_err(|e| {
                    Error::EvalError(format!("Could not read '{}': {}", path.display(), e))
                })?;

                let mut parser = klujur_parser::Parser::new(&content)
                    .map_err(|e| Error::EvalError(format!("{:?}", e)))?;

                while let Some(form) = parser
                    .parse()
                    .map_err(|e| Error::EvalError(format!("{:?}", e)))?
                {
                    eval(&form, env)?;
                }

                registry.mark_loaded(&ns_name);

                // Restore original namespace after loading
                registry.set_current(&original_ns_name);
            } else if registry.find(&ns_name).is_none() {
                // Namespace doesn't exist and no file found
                return Err(Error::EvalError(format!(
                    "Could not locate {} (searched load paths: {:?})",
                    ns_name,
                    registry.load_paths()
                )));
            }
            // If namespace exists but no file, that's OK (might be builtin)
        }

        // Get the original namespace (use find_or_create in case it was just created)
        let current_ns = registry.find_or_create(&original_ns_name);

        // Apply :as alias
        if let Some(alias) = opts.alias
            && let Some(target_ns) = registry.find(&ns_name)
        {
            current_ns.add_alias(alias, target_ns);
        }

        // Apply :refer
        if let Some(refer_spec) = opts.refer
            && let Some(source_ns) = registry.find(&ns_name)
        {
            let publics = source_ns.publics();
            match refer_spec {
                ReferSpec::All => {
                    for (name, var) in publics {
                        current_ns.refer(name, var);
                    }
                }
                ReferSpec::Only(names) => {
                    for name in names {
                        if let Some(var) = publics.get(&name) {
                            current_ns.refer(name, var.clone());
                        } else if source_ns.interns().contains_key(&name) {
                            return Err(Error::EvalError(format!("{} is not public", name)));
                        } else {
                            return Err(Error::EvalError(format!(
                                "{} does not exist in {}",
                                name, ns_name
                            )));
                        }
                    }
                }
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// (use spec...) - Load namespace and refer all public vars (deprecated)
///
/// Equivalent to (require '[ns :refer :all]).
/// Supports :only, :exclude, :rename filters like refer.
fn eval_use(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("use", "requires at least 1 argument"));
    }

    let registry = env.registry();
    // Save the original namespace before processing (files may switch namespaces)
    let original_ns_name = registry.current_name();

    for arg in args {
        let val = eval(arg, env)?;

        // Parse namespace and options
        let (ns_name, only, exclude, rename) = match &val {
            KlujurVal::Symbol(s, _) => (
                s.name().to_string(),
                None,
                vec![],
                std::collections::HashMap::new(),
            ),
            KlujurVal::Vector(items, _) if !items.is_empty() => {
                let ns_name = match &items[0] {
                    KlujurVal::Symbol(s, _) => s.name().to_string(),
                    other => return Err(Error::type_error_in("use", "symbol", other.type_name())),
                };

                let mut only: Option<Vec<String>> = None;
                let mut exclude: Vec<String> = vec![];
                let mut rename: std::collections::HashMap<String, String> =
                    std::collections::HashMap::new();

                let mut i = 1;
                while i < items.len() {
                    match &items[i] {
                        KlujurVal::Keyword(kw) if kw.name() == "only" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Vector(refs, _) = &items[i + 1]
                            {
                                only = Some(
                                    refs.iter()
                                        .filter_map(|v| match v {
                                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                            _ => None,
                                        })
                                        .collect(),
                                );
                            }
                            i += 2;
                        }
                        KlujurVal::Keyword(kw) if kw.name() == "exclude" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Vector(refs, _) = &items[i + 1]
                            {
                                exclude = refs
                                    .iter()
                                    .filter_map(|v| match v {
                                        KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                        _ => None,
                                    })
                                    .collect();
                            }
                            i += 2;
                        }
                        KlujurVal::Keyword(kw) if kw.name() == "rename" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Map(map, _) = &items[i + 1]
                            {
                                for (k, v) in map.iter() {
                                    if let (KlujurVal::Symbol(ks, _), KlujurVal::Symbol(vs, _)) =
                                        (k, v)
                                    {
                                        rename.insert(ks.name().to_string(), vs.name().to_string());
                                    }
                                }
                            }
                            i += 2;
                        }
                        _ => i += 1,
                    }
                }

                (ns_name, only, exclude, rename)
            }
            other => {
                return Err(Error::type_error_in(
                    "use",
                    "symbol or vector",
                    other.type_name(),
                ));
            }
        };

        // Load namespace if not loaded
        if !registry.is_loaded(&ns_name) {
            if let Some(path) = registry.find_namespace_file(&ns_name) {
                let content = std::fs::read_to_string(&path).map_err(|e| {
                    Error::EvalError(format!("Could not read '{}': {}", path.display(), e))
                })?;

                let mut parser = klujur_parser::Parser::new(&content)
                    .map_err(|e| Error::EvalError(format!("{:?}", e)))?;

                while let Some(form) = parser
                    .parse()
                    .map_err(|e| Error::EvalError(format!("{:?}", e)))?
                {
                    eval(&form, env)?;
                }

                registry.mark_loaded(&ns_name);

                // Restore original namespace after loading (file may have switched namespaces)
                registry.set_current(&original_ns_name);
            } else if registry.find(&ns_name).is_none() {
                return Err(Error::EvalError(format!("Could not locate {}", ns_name)));
            }
        }

        // Refer vars from namespace (use original namespace, not whatever the loaded file switched to)
        if let Some(source_ns) = registry.find(&ns_name) {
            let current_ns = registry.find_or_create(&original_ns_name);
            let publics = source_ns.publics();

            let vars_to_refer: Vec<(String, _)> = match only {
                Some(only_list) => only_list
                    .into_iter()
                    .filter(|name| !exclude.contains(name))
                    .filter_map(|name| {
                        publics.get(&name).map(|var| {
                            let refer_name = rename.get(&name).cloned().unwrap_or(name);
                            (refer_name, var.clone())
                        })
                    })
                    .collect(),
                None => publics
                    .into_iter()
                    .filter(|(name, _)| !exclude.contains(name))
                    .map(|(name, var)| {
                        let refer_name = rename.get(&name).cloned().unwrap_or(name);
                        (refer_name, var)
                    })
                    .collect(),
            };

            for (name, var) in vars_to_refer {
                current_ns.refer(name, var);
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// (all-ns) - Returns a sequence of all namespaces
fn eval_all_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::syntax("all-ns", "takes no arguments"));
    }

    let registry = env.registry();
    let ns_names = registry.all_ns();

    let ns_symbols: Vec<KlujurVal> = ns_names
        .into_iter()
        .map(|name| KlujurVal::symbol(Symbol::new(&name)))
        .collect();

    Ok(KlujurVal::list(ns_symbols))
}

/// (find-ns sym) - Returns the namespace named by the symbol, or nil if not found
fn eval_find_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("find-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "find-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    match registry.find(&ns_name) {
        Some(_) => Ok(KlujurVal::symbol(Symbol::new(&ns_name))),
        None => Ok(KlujurVal::Nil),
    }
}

/// (create-ns sym) - Creates a namespace with the given name if it doesn't exist, returns it
fn eval_create_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("create-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "create-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    registry.find_or_create(&ns_name);

    Ok(KlujurVal::symbol(Symbol::new(&ns_name)))
}

/// (remove-ns sym) - Removes the namespace from the registry, returns nil
fn eval_remove_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("remove-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "remove-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    if !registry.remove_ns(&ns_name) {
        // Could not remove - either doesn't exist or is current namespace
        if registry.current_name() == ns_name {
            return Err(Error::EvalError(
                "Cannot remove current namespace".to_string(),
            ));
        }
    }

    Ok(KlujurVal::Nil)
}

/// (the-ns sym) - Returns the namespace named by the symbol, throws if not found
fn eval_the_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("the-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "the-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    match registry.find(&ns_name) {
        Some(_) => Ok(KlujurVal::symbol(Symbol::new(&ns_name))),
        None => Err(Error::EvalError(format!("No namespace: {}", ns_name))),
    }
}

/// (ns-name ns) - Returns the name of the namespace as a symbol
fn eval_ns_name(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-name", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "ns-name",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    // Verify namespace exists
    let registry = env.registry();
    registry
        .find(&ns_name)
        .ok_or_else(|| Error::EvalError(format!("No namespace: {}", ns_name)))?;

    Ok(KlujurVal::symbol(Symbol::new(&ns_name)))
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
            let params_vec: Vec<KlujurVal> = match &arity_list[0] {
                KlujurVal::Vector(v, _) => v.iter().cloned().collect(),
                other => {
                    return Err(Error::syntax(
                        "defmacro",
                        format!("parameter vector expected, got {}", other.type_name()),
                    ));
                }
            };
            let (params, rest_param) = parse_params(&params_vec)?;
            let body: Vec<KlujurVal> = arity_list[1..].to_vec();
            arities.push(FnArity::new(params, rest_param, body));
        }
        arities
    } else {
        // Single-arity: (defmacro name [params] body...)
        let params_vec: Vec<KlujurVal> = match &rest[0] {
            KlujurVal::Vector(v, _) => v.iter().cloned().collect(),
            other => {
                return Err(Error::syntax(
                    "defmacro",
                    format!("parameter vector expected, got {}", other.type_name()),
                ));
            }
        };
        let (params, rest_param) = parse_params(&params_vec)?;
        let body: Vec<KlujurVal> = rest[1..].to_vec();

        if body.is_empty() {
            return Err(Error::syntax("defmacro", "requires a body"));
        }
        vec![FnArity::new(params, rest_param, body)]
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

/// Helper to parse parameter vector into params and rest param
fn parse_params(params_vec: &[KlujurVal]) -> Result<(Vec<Symbol>, Option<Symbol>)> {
    let mut params = Vec::new();
    let mut rest_param = None;
    let mut found_amp = false;

    for param in params_vec {
        match param {
            KlujurVal::Symbol(s, _) if s.name() == "&" => {
                found_amp = true;
            }
            KlujurVal::Symbol(s, _) => {
                if found_amp {
                    rest_param = Some(s.clone());
                } else {
                    params.push(s.clone());
                }
            }
            other => {
                return Err(Error::syntax(
                    "defmacro",
                    format!("parameter must be a symbol, got {}", other.type_name()),
                ));
            }
        }
    }

    Ok((params, rest_param))
}

// ============================================================================
// Multimethods
// ============================================================================

/// (defmulti name dispatch-fn & options) - define a multimethod
/// Options:
///   :hierarchy h - use hierarchy h for isa? dispatch (defaults to global hierarchy)
fn eval_defmulti(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::KlujurHierarchy;
    use std::cell::RefCell;

    if args.is_empty() {
        return Err(Error::syntax("defmulti", "requires a name"));
    }

    // Get the name
    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defmulti",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    if args.len() < 2 {
        return Err(Error::syntax("defmulti", "requires a dispatch function"));
    }

    // Evaluate the dispatch function
    let dispatch_fn = eval(&args[1], env)?;

    // Parse options (keyword-value pairs after dispatch-fn)
    let mut hierarchy: Option<Rc<RefCell<KlujurHierarchy>>> = None;

    let mut i = 2;
    while i < args.len() {
        match &args[i] {
            KlujurVal::Keyword(kw) if kw.name() == "hierarchy" && kw.namespace().is_none() => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax("defmulti", ":hierarchy requires a value"));
                }
                let h_val = eval(&args[i + 1], env)?;
                match h_val {
                    KlujurVal::Hierarchy(h) => {
                        hierarchy = Some(h);
                    }
                    other => {
                        return Err(Error::type_error_in(
                            "defmulti :hierarchy",
                            "hierarchy",
                            other.type_name(),
                        ));
                    }
                }
                i += 2;
            }
            KlujurVal::Keyword(kw) => {
                return Err(Error::syntax(
                    "defmulti",
                    format!("unknown option :{}", kw.name()),
                ));
            }
            other => {
                return Err(Error::syntax(
                    "defmulti",
                    format!("expected keyword option, got {}", other.type_name()),
                ));
            }
        }
    }

    // Create the multimethod with optional hierarchy
    let mm = if let Some(h) = hierarchy {
        KlujurMultimethod::with_hierarchy(name.clone(), dispatch_fn, h)
    } else {
        // Use global hierarchy by default
        let global_h = env.registry().global_hierarchy();
        KlujurMultimethod::with_hierarchy(name.clone(), dispatch_fn, global_h)
    };

    // Intern as a Var in the current namespace
    let registry = env.registry();
    let current_ns = registry.current();
    let var = current_ns.intern_with_value(name.name(), KlujurVal::Multimethod(Rc::new(mm)));

    Ok(KlujurVal::Var(var))
}

/// (defmethod multimethod dispatch-val [params] body...) - add a method to a multimethod
fn eval_defmethod(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::FnArity;

    if args.len() < 3 {
        return Err(Error::syntax(
            "defmethod",
            "requires multimethod name, dispatch value, params, and body",
        ));
    }

    // Get the multimethod name and resolve it
    let mm_name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defmethod",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    // Resolve the multimethod
    let registry = env.registry();
    let mm_var = registry
        .current()
        .resolve(&mm_name)
        .ok_or_else(|| Error::EvalError(format!("Undefined: {}", mm_name)))?;

    let mm_val = deref_var(&mm_var);
    let mm = match &mm_val {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "defmethod",
                "multimethod",
                other.type_name(),
            ));
        }
    };

    // Evaluate the dispatch value
    let dispatch_val = eval(&args[1], env)?;

    // Parse the params vector and body using parse_fn_arity for destructuring support
    let (params, rest_param, patterns, rest_pattern, body) = parse_fn_arity(&args[2], &args[3..])?;

    // Create the method function with destructuring support
    let arity = FnArity::with_patterns(params, rest_param, patterns, rest_pattern, body);
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let method_fn = KlujurFn::new_multi(None, vec![arity], env_any);
    let method = KlujurVal::Fn(method_fn);

    // Add the method to the multimethod
    mm.add_method(dispatch_val, method);

    // Return the multimethod
    Ok(KlujurVal::Multimethod(mm))
}

/// (derive child parent) - establishes a parent/child relationship in the global hierarchy
/// (derive h child parent) - establishes a parent/child relationship in hierarchy h
fn eval_derive(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            // (derive child parent) - uses global hierarchy
            let child = eval(&args[0], env)?;
            let parent = eval(&args[1], env)?;
            let hierarchy = env.registry().global_hierarchy();
            hierarchy
                .borrow_mut()
                .derive(child, parent)
                .map_err(Error::EvalError)?;
            Ok(KlujurVal::Nil)
        }
        3 => {
            // (derive h child parent) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let child = eval(&args[1], env)?;
            let parent = eval(&args[2], env)?;
            match h {
                KlujurVal::Hierarchy(h) => {
                    h.borrow_mut()
                        .derive(child, parent)
                        .map_err(Error::EvalError)?;
                    Ok(KlujurVal::Hierarchy(h))
                }
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "derive expects 2 or 3 arguments, got {}",
            n
        ))),
    }
}

/// (underive child parent) - removes a parent/child relationship from the global hierarchy
/// (underive h child parent) - removes a parent/child relationship from hierarchy h
fn eval_underive(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            // (underive child parent) - uses global hierarchy
            let child = eval(&args[0], env)?;
            let parent = eval(&args[1], env)?;
            let hierarchy = env.registry().global_hierarchy();
            hierarchy.borrow_mut().underive(&child, &parent);
            Ok(KlujurVal::Nil)
        }
        3 => {
            // (underive h child parent) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let child = eval(&args[1], env)?;
            let parent = eval(&args[2], env)?;
            match h {
                KlujurVal::Hierarchy(h) => {
                    h.borrow_mut().underive(&child, &parent);
                    Ok(KlujurVal::Hierarchy(h))
                }
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "underive expects 2 or 3 arguments, got {}",
            n
        ))),
    }
}

/// (isa? child parent) - returns true if child derives from parent (using global hierarchy)
/// (isa? h child parent) - returns true if child derives from parent (using hierarchy h)
fn eval_isa(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            // (isa? child parent) - uses global hierarchy
            let child = eval(&args[0], env)?;
            let parent = eval(&args[1], env)?;
            let hierarchy = env.registry().global_hierarchy();
            Ok(KlujurVal::Bool(hierarchy.borrow().isa(&child, &parent)))
        }
        3 => {
            // (isa? h child parent) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let child = eval(&args[1], env)?;
            let parent = eval(&args[2], env)?;
            match h {
                KlujurVal::Hierarchy(h) => Ok(KlujurVal::Bool(h.borrow().isa(&child, &parent))),
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "isa? expects 2 or 3 arguments, got {}",
            n
        ))),
    }
}

/// (parents child) - returns the immediate parents of child (using global hierarchy)
/// (parents h child) - returns the immediate parents of child (using hierarchy h)
fn eval_parents(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (parents child) - uses global hierarchy
            let child = eval(&args[0], env)?;
            let hierarchy = env.registry().global_hierarchy();
            let parents = hierarchy.borrow().parents(&child);
            Ok(KlujurVal::set(parents.into_iter().collect()))
        }
        2 => {
            // (parents h child) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let child = eval(&args[1], env)?;
            match h {
                KlujurVal::Hierarchy(h) => {
                    let parents = h.borrow().parents(&child);
                    Ok(KlujurVal::set(parents.into_iter().collect()))
                }
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "parents expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

/// (ancestors child) - returns all ancestors of child (using global hierarchy)
/// (ancestors h child) - returns all ancestors of child (using hierarchy h)
fn eval_ancestors(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (ancestors child) - uses global hierarchy
            let child = eval(&args[0], env)?;
            let hierarchy = env.registry().global_hierarchy();
            let ancestors = hierarchy.borrow().ancestors(&child);
            Ok(KlujurVal::set(ancestors.into_iter().collect()))
        }
        2 => {
            // (ancestors h child) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let child = eval(&args[1], env)?;
            match h {
                KlujurVal::Hierarchy(h) => {
                    let ancestors = h.borrow().ancestors(&child);
                    Ok(KlujurVal::set(ancestors.into_iter().collect()))
                }
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "ancestors expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

/// (descendants parent) - returns all descendants of parent (using global hierarchy)
/// (descendants h parent) - returns all descendants of parent (using hierarchy h)
fn eval_descendants(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (descendants parent) - uses global hierarchy
            let parent = eval(&args[0], env)?;
            let hierarchy = env.registry().global_hierarchy();
            let descendants = hierarchy.borrow().descendants(&parent);
            Ok(KlujurVal::set(descendants.into_iter().collect()))
        }
        2 => {
            // (descendants h parent) - uses provided hierarchy
            let h = eval(&args[0], env)?;
            let parent = eval(&args[1], env)?;
            match h {
                KlujurVal::Hierarchy(h) => {
                    let descendants = h.borrow().descendants(&parent);
                    Ok(KlujurVal::set(descendants.into_iter().collect()))
                }
                other => Err(Error::type_error("hierarchy", other.type_name())),
            }
        }
        n => Err(Error::EvalError(format!(
            "descendants expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

// ============================================================================
// Protocol Special Forms
// ============================================================================

/// (defprotocol Name
///   "Optional docstring"
///   (method-name [this arg1 arg2] "Method docstring")
///   (other-method [this] [this x] "Multiple arities"))
fn eval_defprotocol(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::{MethodSignature, Protocol};

    if args.is_empty() {
        return Err(Error::syntax("defprotocol", "requires a name"));
    }

    // Get the protocol name
    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defprotocol",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    let registry = env.registry();
    let ns_name = registry.current_name();

    // Create the protocol
    let mut protocol = Protocol::new(name.clone(), ns_name.clone());

    let mut i = 1;

    // Skip docstring if present
    if args
        .get(i)
        .map(|v| matches!(v, KlujurVal::String(_)))
        .unwrap_or(false)
    {
        i += 1;
    }

    // Parse method signatures
    while i < args.len() {
        let method_form = match &args[i] {
            KlujurVal::List(items, _) => items.iter().cloned().collect::<Vec<_>>(),
            other => {
                return Err(Error::syntax(
                    "defprotocol",
                    format!("method signature must be a list, got {}", other.type_name()),
                ));
            }
        };

        if method_form.is_empty() {
            return Err(Error::syntax(
                "defprotocol",
                "method signature cannot be empty",
            ));
        }

        let method_name = match &method_form[0] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "defprotocol",
                    format!("method name must be a symbol, got {}", other.type_name()),
                ));
            }
        };

        let mut arglists = Vec::new();
        let mut doc = None;

        for item in method_form.iter().skip(1) {
            match item {
                KlujurVal::Vector(params, _) => {
                    // Parse arglist
                    let mut arg_symbols = Vec::new();
                    for param in params.iter() {
                        if let KlujurVal::Symbol(s, _) = param {
                            arg_symbols.push(s.clone());
                        }
                    }
                    arglists.push(arg_symbols);
                }
                KlujurVal::String(s) => {
                    doc = Some(s.to_string());
                }
                _ => {}
            }
        }

        if arglists.is_empty() {
            return Err(Error::syntax(
                "defprotocol",
                format!("method {} requires at least one arglist", method_name),
            ));
        }

        protocol.add_method(MethodSignature {
            name: method_name.clone(),
            arglists,
            doc,
        });

        i += 1;
    }

    // Register the protocol
    let proto_rc = registry.register_protocol(protocol);

    // Create dispatch functions for each method and intern them as vars
    let current_ns = registry.current();
    for method_name_str in proto_rc.methods.keys() {
        let dispatch_fn = create_protocol_dispatch_fn(proto_rc.clone(), method_name_str.clone());
        current_ns.intern_with_value(method_name_str.clone(), dispatch_fn);
    }

    // Also intern the protocol itself as a var
    let proto_val = KlujurVal::from_protocol(proto_rc);
    current_ns.intern_with_value(name.name().to_string(), proto_val.clone());

    Ok(proto_val)
}

/// Create a protocol dispatch function.
/// This returns a NativeFn that dispatches based on the first argument's type.
fn create_protocol_dispatch_fn(
    protocol: Rc<klujur_parser::Protocol>,
    method_name: String,
) -> KlujurVal {
    let proto = protocol.clone();
    let name = method_name.clone();

    // Create a closure that performs protocol dispatch
    let dispatch_fn = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.is_empty() {
            return Err(Error::EvalError(format!(
                "Protocol method {} requires at least one argument",
                name
            )));
        }

        let first_arg = &args[0];
        let type_key = first_arg.type_key();

        // Look up the implementation for this type
        let impls = proto.impls.borrow();
        let type_impl = impls.get(&type_key).ok_or_else(|| {
            Error::EvalError(format!(
                "No implementation of method {} for type {:?}",
                name, type_key
            ))
        })?;

        let method_fn = type_impl.methods.get(&name).ok_or_else(|| {
            Error::EvalError(format!(
                "Method {} not implemented for type {:?}",
                name, type_key
            ))
        })?;

        // Apply the method function with the args
        apply(method_fn, args)
    };

    KlujurVal::NativeFn(make_native_fn(
        Box::leak(method_name.into_boxed_str()),
        dispatch_fn,
    ))
}

/// (extend-type TypeName
///   ProtocolName
///   (method-name [this arg] body)
///   ...)
fn eval_extend_type(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::Symbol;

    if args.is_empty() {
        return Err(Error::syntax("extend-type", "requires a type name"));
    }

    // Get the type name
    let type_name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "extend-type",
                format!(
                    "first argument must be a type symbol, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let type_key = symbol_to_type_key(&type_name)?;
    let registry = env.registry();

    let mut i = 1;
    while i < args.len() {
        // Get protocol name
        let protocol_name = match &args[i] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "extend-type",
                    format!("expected protocol name, got {}", other.type_name()),
                ));
            }
        };

        // Find the protocol
        let protocol = registry
            .resolve_protocol(protocol_name.name())
            .ok_or_else(|| Error::EvalError(format!("Unknown protocol: {}", protocol_name)))?;

        i += 1;

        // Collect method implementations until next protocol name or end
        while i < args.len() {
            // Check if this is a method implementation (list starting with symbol)
            match &args[i] {
                KlujurVal::List(items, _) if !items.is_empty() => {
                    if let KlujurVal::Symbol(method_sym, _) = &items[0] {
                        let method_name = method_sym.name().to_string();

                        // Check if this method exists in the protocol
                        if !protocol.methods.contains_key(&method_name) {
                            return Err(Error::EvalError(format!(
                                "Method {} is not part of protocol {}",
                                method_name, protocol_name
                            )));
                        }

                        // Build a function from (method-name [args] body)
                        // Convert to (fn [args] body)
                        let fn_args: Vec<KlujurVal> = items.iter().skip(1).cloned().collect();
                        let fn_form = KlujurVal::list(
                            std::iter::once(KlujurVal::Symbol(Symbol::new("fn"), None))
                                .chain(fn_args)
                                .collect(),
                        );

                        // Evaluate the fn form to create the function
                        let method_fn = eval(&fn_form, env)?;

                        // Add the method implementation to the protocol
                        protocol.add_method_impl(type_key.clone(), method_name, method_fn);

                        i += 1;
                    } else {
                        // Not a method impl, must be next protocol
                        break;
                    }
                }
                KlujurVal::Symbol(_, _) => {
                    // This is the next protocol name
                    break;
                }
                other => {
                    return Err(Error::syntax(
                        "extend-type",
                        format!(
                            "expected method implementation or protocol name, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// Convert a type name symbol to a TypeKey
fn symbol_to_type_key(sym: &klujur_parser::Symbol) -> Result<klujur_parser::TypeKey> {
    use klujur_parser::TypeKey;

    match sym.name() {
        "nil" => Ok(TypeKey::Nil),
        "Boolean" | "Bool" => Ok(TypeKey::Bool),
        "Integer" | "Long" | "Int" => Ok(TypeKey::Int),
        "Float" | "Double" => Ok(TypeKey::Float),
        "Ratio" => Ok(TypeKey::Ratio),
        "Char" | "Character" => Ok(TypeKey::Char),
        "String" => Ok(TypeKey::String),
        "Symbol" => Ok(TypeKey::Symbol),
        "Keyword" => Ok(TypeKey::Keyword),
        "List" | "PersistentList" => Ok(TypeKey::List),
        "Vector" | "PersistentVector" => Ok(TypeKey::Vector),
        "Map" | "HashMap" | "PersistentHashMap" => Ok(TypeKey::Map),
        "Set" | "HashSet" | "PersistentHashSet" => Ok(TypeKey::Set),
        "Fn" | "Function" | "IFn" => Ok(TypeKey::Fn),
        "Var" => Ok(TypeKey::Var),
        "Atom" => Ok(TypeKey::Atom),
        "Delay" => Ok(TypeKey::Delay),
        "LazySeq" => Ok(TypeKey::LazySeq),
        "Multimethod" => Ok(TypeKey::Multimethod),
        "Hierarchy" => Ok(TypeKey::Hierarchy),
        "Reduced" => Ok(TypeKey::Reduced),
        "Volatile" => Ok(TypeKey::Volatile),
        name => Ok(TypeKey::Record(klujur_parser::Symbol::new(name))),
    }
}

// ============================================================================
// Record Special Forms
// ============================================================================

/// (defrecord RecordName [field1 field2 ...]
///   ProtocolName
///   (method-name [this arg] body)
///   ...)
fn eval_defrecord(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    use klujur_parser::{RecordDef, Symbol};

    if args.is_empty() {
        return Err(Error::syntax("defrecord", "requires a name"));
    }

    // Get the record name
    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defrecord",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    if args.len() < 2 {
        return Err(Error::syntax("defrecord", "requires a field vector"));
    }

    // Get the field vector
    let fields: Vec<Symbol> = match &args[1] {
        KlujurVal::Vector(items, _) => {
            let mut fields = Vec::new();
            for item in items.iter() {
                match item {
                    KlujurVal::Symbol(s, _) => fields.push(s.clone()),
                    other => {
                        return Err(Error::syntax(
                            "defrecord",
                            format!("field must be a symbol, got {}", other.type_name()),
                        ));
                    }
                }
            }
            fields
        }
        other => {
            return Err(Error::syntax(
                "defrecord",
                format!(
                    "second argument must be a vector, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let registry = env.registry();
    let current_ns_name = registry.current_name();

    // Create and register the record definition
    let record_def = RecordDef::new(name.clone(), current_ns_name.clone(), fields.clone());
    registry.register_record(record_def);

    // Create positional constructor: ->RecordName
    let positional_ctor =
        create_positional_record_constructor(name.clone(), current_ns_name.clone(), fields.clone());
    let ctor_name = format!("->{}", name.name());
    let current_ns = registry.current();
    current_ns.intern_with_value(&ctor_name, positional_ctor);

    // Create map constructor: map->RecordName
    let map_ctor =
        create_map_record_constructor(name.clone(), current_ns_name.clone(), fields.clone());
    let map_ctor_name = format!("map->{}", name.name());
    current_ns.intern_with_value(&map_ctor_name, map_ctor);

    // Parse inline protocol implementations (args[2..])
    let mut i = 2;
    while i < args.len() {
        // Expect a protocol name
        let protocol_name = match &args[i] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "defrecord",
                    format!("expected protocol name symbol, got {}", other.type_name()),
                ));
            }
        };
        i += 1;

        // Look up the protocol
        let protocol = registry
            .resolve_protocol(protocol_name.name())
            .ok_or_else(|| Error::EvalError(format!("Protocol not found: {}", protocol_name)))?;

        // Collect method implementations until we hit another symbol or end
        while i < args.len() {
            match &args[i] {
                KlujurVal::List(items, _) => {
                    let method_form: Vec<_> = items.iter().cloned().collect();
                    if method_form.is_empty() {
                        return Err(Error::syntax(
                            "defrecord",
                            "method implementation cannot be empty",
                        ));
                    }

                    // Parse method: (method-name [args] body...)
                    let method_name = match &method_form[0] {
                        KlujurVal::Symbol(s, _) => s.name().to_string(),
                        other => {
                            return Err(Error::syntax(
                                "defrecord",
                                format!("method name must be a symbol, got {}", other.type_name()),
                            ));
                        }
                    };

                    // Parse args vector and body
                    if method_form.len() < 2 {
                        return Err(Error::syntax(
                            "defrecord",
                            format!("method {} requires args and body", method_name),
                        ));
                    }

                    let params_vec = match &method_form[1] {
                        KlujurVal::Vector(v, _) => v.iter().cloned().collect::<Vec<_>>(),
                        other => {
                            return Err(Error::syntax(
                                "defrecord",
                                format!(
                                    "method {} args must be a vector, got {}",
                                    method_name,
                                    other.type_name()
                                ),
                            ));
                        }
                    };

                    let body = method_form[2..].to_vec();

                    // Parse param symbols
                    let params: Vec<Symbol> = params_vec
                        .iter()
                        .map(|p| match p {
                            KlujurVal::Symbol(s, _) => Ok(s.clone()),
                            other => Err(Error::syntax(
                                "defrecord",
                                format!("param must be symbol, got {}", other.type_name()),
                            )),
                        })
                        .collect::<Result<Vec<_>>>()?;

                    // Create the method function
                    let method_fn = create_fn_from_parts(params, body, env.clone());

                    // Register the implementation
                    let type_key = klujur_parser::TypeKey::Record(name.clone());
                    protocol.add_method_impl(type_key, method_name, method_fn);

                    i += 1;
                }
                KlujurVal::Symbol(_, _) => {
                    // This is the next protocol name
                    break;
                }
                other => {
                    return Err(Error::syntax(
                        "defrecord",
                        format!(
                            "expected method implementation or protocol name, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }
        }
    }

    // Return the record name symbol
    Ok(KlujurVal::Symbol(name, None))
}

/// Create a positional constructor function: ->RecordName
fn create_positional_record_constructor(
    record_type: klujur_parser::Symbol,
    record_ns: String,
    fields: Vec<klujur_parser::Symbol>,
) -> KlujurVal {
    use klujur_parser::{Keyword, RecordInstance};
    use std::collections::HashMap;

    let arity = fields.len();
    let name = format!("->{}", record_type.name());

    let constructor = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.len() != arity {
            return Err(Error::arity(arity, args.len()));
        }

        let mut values = HashMap::new();
        for (field, value) in fields.iter().zip(args.iter()) {
            let key = Keyword::new(field.name());
            values.insert(key, value.clone());
        }

        Ok(KlujurVal::record(RecordInstance::new(
            record_type.clone(),
            record_ns.clone(),
            fields.clone(),
            values,
        )))
    };

    KlujurVal::NativeFn(make_native_fn(
        Box::leak(name.into_boxed_str()),
        constructor,
    ))
}

/// Create a map constructor function: map->RecordName
fn create_map_record_constructor(
    record_type: klujur_parser::Symbol,
    record_ns: String,
    fields: Vec<klujur_parser::Symbol>,
) -> KlujurVal {
    use klujur_parser::{Keyword, RecordInstance};
    use std::collections::HashMap;

    let name = format!("map->{}", record_type.name());

    let constructor = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.len() != 1 {
            return Err(Error::arity(1, args.len()));
        }

        let map = match &args[0] {
            KlujurVal::Map(m, _) => m,
            other => {
                return Err(Error::type_error("map", other.type_name()));
            }
        };

        let mut values = HashMap::new();

        // Extract required fields
        for field in &fields {
            let key = KlujurVal::Keyword(Keyword::new(field.name()));
            let value = map.get(&key).ok_or_else(|| {
                Error::EvalError(format!("Missing required field: {}", field.name()))
            })?;
            values.insert(Keyword::new(field.name()), value.clone());
        }

        // Include any extra keys from the map
        for (k, v) in map.iter() {
            if let KlujurVal::Keyword(kw) = k
                && !values.contains_key(kw)
            {
                values.insert(kw.clone(), v.clone());
            }
        }

        Ok(KlujurVal::record(RecordInstance::new(
            record_type.clone(),
            record_ns.clone(),
            fields.clone(),
            values,
        )))
    };

    KlujurVal::NativeFn(make_native_fn(
        Box::leak(name.into_boxed_str()),
        constructor,
    ))
}

/// Helper to create a function from params and body
fn create_fn_from_parts(
    params: Vec<klujur_parser::Symbol>,
    body: Vec<KlujurVal>,
    env: Env,
) -> KlujurVal {
    use klujur_parser::{FnArity, KlujurFn};
    use std::any::Any;

    let arity = FnArity::new(params, None, body);
    let env_any: Rc<dyn Any> = Rc::new(env);
    KlujurVal::Fn(KlujurFn::new_multi(None, vec![arity], env_any))
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

// ============================================================================
// Exception Handling
// ============================================================================

/// (throw expr) - throw an exception
fn eval_throw(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("throw", "requires exactly 1 argument"));
    }

    let val = eval(&args[0], env)?;
    Err(Error::Thrown(val))
}

/// (try body... (catch type binding handler...)... (finally cleanup...))
/// Evaluates body forms, catches exceptions, and runs cleanup.
fn eval_try(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Parse body, catch clauses, and finally clause
    let mut body = Vec::new();
    let mut catch_clauses: Vec<(KlujurVal, Symbol, Vec<KlujurVal>)> = Vec::new();
    let mut finally_clause: Option<Vec<KlujurVal>> = None;

    for arg in args {
        if let KlujurVal::List(items, _) = arg
            && let Some(KlujurVal::Symbol(sym, _)) = items.front()
        {
            match sym.name() {
                "catch" => {
                    // (catch type binding handler...)
                    if items.len() < 3 {
                        return Err(Error::syntax(
                            "try",
                            "catch requires type, binding, and body",
                        ));
                    }
                    let catch_type = items[1].clone();
                    let binding = match &items[2] {
                        KlujurVal::Symbol(s, _) => s.clone(),
                        other => {
                            return Err(Error::syntax(
                                "try",
                                format!(
                                    "catch binding must be a symbol, got {}",
                                    other.type_name()
                                ),
                            ));
                        }
                    };
                    let handler: Vec<KlujurVal> = items.iter().skip(3).cloned().collect();
                    catch_clauses.push((catch_type, binding, handler));
                    continue;
                }
                "finally" => {
                    // (finally cleanup...)
                    if finally_clause.is_some() {
                        return Err(Error::syntax("try", "only one finally clause allowed"));
                    }
                    finally_clause = Some(items.iter().skip(1).cloned().collect());
                    continue;
                }
                _ => {}
            }
        }
        // Not a catch or finally - it's part of the body
        body.push(arg.clone());
    }

    // Evaluate body
    let result = eval_try_body(&body, &catch_clauses, env);

    // Always run finally, regardless of success or failure
    if let Some(finally_body) = &finally_clause {
        for expr in finally_body {
            // Evaluate finally but ignore its result (and any errors from it)
            let _ = eval(expr, env);
        }
    }

    result
}

/// Evaluate try body and handle exceptions with catch clauses
fn eval_try_body(
    body: &[KlujurVal],
    catch_clauses: &[(KlujurVal, Symbol, Vec<KlujurVal>)],
    env: &Env,
) -> Result<KlujurVal> {
    // Evaluate body - use closure to capture errors properly
    let body_result: Result<KlujurVal> = (|| {
        let mut result = KlujurVal::Nil;
        for expr in body {
            result = eval(expr, env)?;
        }
        Ok(result)
    })();

    match body_result {
        Ok(val) => Ok(val),
        Err(Error::Thrown(thrown_val)) => {
            // Try to match a catch clause
            for (catch_type, binding, handler) in catch_clauses {
                if matches_catch_type(catch_type, &thrown_val) {
                    // Create new environment with exception bound
                    let catch_env = env.child();
                    catch_env.define(binding.clone(), thrown_val.clone());

                    // Evaluate handler
                    let mut result = KlujurVal::Nil;
                    for expr in handler {
                        result = eval(expr, &catch_env)?;
                    }
                    return Ok(result);
                }
            }
            // No catch matched, re-throw
            Err(Error::Thrown(thrown_val))
        }
        Err(other_error) => {
            // Non-thrown errors (like ArityError, TypeError, etc.)
            // Convert to a thrown exception so catch can handle them
            for (catch_type, binding, handler) in catch_clauses {
                // :default catches all errors
                if matches!(catch_type, KlujurVal::Keyword(kw) if kw.name() == "default") {
                    let catch_env = env.child();
                    // Create an exception map for non-thrown errors
                    let error_val = KlujurVal::map(vec![
                        (
                            KlujurVal::Keyword(klujur_parser::Keyword::new("message")),
                            KlujurVal::string(other_error.to_string()),
                        ),
                        (
                            KlujurVal::Keyword(klujur_parser::Keyword::new("type")),
                            KlujurVal::Keyword(klujur_parser::Keyword::new("error")),
                        ),
                    ]);
                    catch_env.define(binding.clone(), error_val);

                    let mut result = KlujurVal::Nil;
                    for expr in handler {
                        result = eval(expr, &catch_env)?;
                    }
                    return Ok(result);
                }
            }
            // No catch matched, re-throw original error
            Err(other_error)
        }
    }
}

/// Check if a catch type matches the thrown value
fn matches_catch_type(catch_type: &KlujurVal, _thrown: &KlujurVal) -> bool {
    match catch_type {
        // :default catches everything
        KlujurVal::Keyword(kw) if kw.name() == "default" => true,
        // Throwable catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Throwable" => true,
        // Exception catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Exception" => true,
        // Object catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Object" => true,
        // Future: support matching by :type in exception maps
        _ => false,
    }
}

// ============================================================================
// Dynamic Binding
// ============================================================================

/// (binding [var1 val1 var2 val2 ...] body...)
/// Establishes thread-local bindings for dynamic vars.
fn eval_binding(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("binding", "requires a binding vector"));
    }

    let bindings_vec: Vec<KlujurVal> = match &args[0] {
        KlujurVal::Vector(v, _) => v.iter().cloned().collect(),
        _ => {
            return Err(Error::syntax(
                "binding",
                "first argument must be a binding vector",
            ));
        }
    };

    if !bindings_vec.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "binding",
            "binding vector must have even number of forms",
        ));
    }

    // First pass: validate all vars are dynamic and collect them
    let mut vars: Vec<KlujurVar> = Vec::new();
    for pair in bindings_vec.chunks(2) {
        let var_sym = match &pair[0] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "binding",
                    format!("binding target must be a symbol, got {}", other.type_name()),
                ));
            }
        };

        // Look up the var (check both lexical env and namespace)
        let var_val = lookup_symbol(&var_sym, env)?;
        let var = match var_val {
            KlujurVal::Var(v) => v,
            other => {
                return Err(Error::syntax(
                    "binding",
                    format!("can only bind vars, {} is a {}", var_sym, other.type_name()),
                ));
            }
        };

        // Check that the var is dynamic
        if !var.is_dynamic() {
            return Err(Error::syntax(
                "binding",
                format!(
                    "can't dynamically bind non-dynamic var: {}",
                    var.qualified_name()
                ),
            ));
        }

        vars.push(var);
    }

    // Second pass: evaluate all values
    let mut vals: Vec<KlujurVal> = Vec::new();
    for pair in bindings_vec.chunks(2) {
        vals.push(eval(&pair[1], env)?);
    }

    // Create binding pairs
    let binding_refs: Vec<(&KlujurVar, KlujurVal)> = vars.iter().zip(vals).collect();

    // Push the bindings (returns a guard that pops on drop)
    let _guard = push_bindings(binding_refs);

    // Evaluate body
    let body = &args[1..];
    let mut result = KlujurVal::Nil;
    for expr in body {
        result = eval(expr, env)?;
    }

    Ok(result)
    // _guard drops here, popping the bindings
}

/// (set! var val) - set a thread-local binding
/// Only works within a binding context for dynamic vars.
fn eval_set_bang(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::syntax("set!", "requires exactly 2 arguments"));
    }

    let var_sym = match &args[0] {
        KlujurVal::Symbol(s, _) => s,
        other => {
            return Err(Error::syntax(
                "set!",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    // Look up the var (check both lexical env and namespace)
    let var_val = lookup_symbol(var_sym, env)?;
    let var = match var_val {
        KlujurVal::Var(v) => v,
        other => {
            return Err(Error::syntax(
                "set!",
                format!("can only set vars, {} is a {}", var_sym, other.type_name()),
            ));
        }
    };

    // Check that the var is dynamic
    if !var.is_dynamic() {
        return Err(Error::syntax(
            "set!",
            format!(
                "can't set non-dynamic var: {}. Use def to change the root value.",
                var.qualified_name()
            ),
        ));
    }

    // Evaluate the new value
    let val = eval(&args[1], env)?;

    // Try to set the thread-local binding
    if set_thread_binding(&var, val.clone()) {
        Ok(val)
    } else {
        Err(Error::syntax(
            "set!",
            format!(
                "can't set {} outside of binding context",
                var.qualified_name()
            ),
        ))
    }
}

/// (swap! atom f & args) - Apply f to current value, update atom with result
fn eval_swap(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::syntax("swap!", "requires at least 2 arguments"));
    }

    let atom_val = eval(&args[0], env)?;
    let atom = match &atom_val {
        KlujurVal::Atom(a) => a,
        other => {
            return Err(Error::type_error_in("swap!", "atom", other.type_name()));
        }
    };

    let f = eval(&args[1], env)?;

    // Evaluate additional arguments
    let mut extra_args = Vec::new();
    for arg in &args[2..] {
        extra_args.push(eval(arg, env)?);
    }

    // Get current value, apply f, update atom
    let current = atom.deref();

    // Build the function call args: (f current-val & extra-args)
    let mut call_args = vec![current];
    call_args.extend(extra_args);

    let new_val = apply(&f, &call_args)?;
    atom.set_value(new_val.clone());

    Ok(new_val)
}

/// (swap-vals! atom f & args) - Like swap!, returns [old new]
fn eval_swap_vals(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::syntax("swap-vals!", "requires at least 2 arguments"));
    }

    let atom_val = eval(&args[0], env)?;
    let atom = match &atom_val {
        KlujurVal::Atom(a) => a,
        other => {
            return Err(Error::type_error_in(
                "swap-vals!",
                "atom",
                other.type_name(),
            ));
        }
    };

    let f = eval(&args[1], env)?;

    // Evaluate additional arguments
    let mut extra_args = Vec::new();
    for arg in &args[2..] {
        extra_args.push(eval(arg, env)?);
    }

    // Get current value, apply f, update atom
    let old_val = atom.deref();

    // Build the function call args: (f current-val & extra-args)
    let mut call_args = vec![old_val.clone()];
    call_args.extend(extra_args);

    let new_val = apply(&f, &call_args)?;
    atom.set_value(new_val.clone());

    Ok(KlujurVal::vector(vec![old_val, new_val]))
}

/// (delay & body) - Create a delay that will evaluate body on first deref
fn eval_delay(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("delay", "requires a body"));
    }

    // Wrap the body in a thunk (zero-arg function)
    // The thunk captures the environment so it can be evaluated later
    use klujur_parser::FnArity;
    use std::any::Any;

    let body: Vec<KlujurVal> = args.to_vec();
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let thunk = KlujurFn::new_multi(
        None, // no name
        vec![FnArity::new(vec![], None, body)],
        env_any,
    );

    Ok(KlujurVal::delay(KlujurVal::Fn(thunk)))
}

/// (lazy-seq & body) - Create a lazy sequence that evaluates body when first accessed
///
/// The body should evaluate to nil (empty sequence) or a cons cell/sequence.
/// Results are cached after first evaluation.
fn eval_lazy_seq(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Wrap the body in a thunk (zero-arg function)
    // The thunk captures the environment so it can be evaluated later
    use klujur_parser::FnArity;
    use std::any::Any;

    let body: Vec<KlujurVal> = args.to_vec();
    let env_any: Rc<dyn Any> = Rc::new(env.clone());
    let thunk = KlujurFn::new_multi(
        None, // no name
        vec![FnArity::new(vec![], None, body)],
        env_any,
    );

    Ok(KlujurVal::lazy_seq(thunk))
}

/// (force x) - Force evaluation of delay (or return x if not a delay)
fn eval_force(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("force", "requires exactly 1 argument"));
    }

    let val = eval(&args[0], env)?;

    match &val {
        KlujurVal::Delay(d) => {
            // If already realized, return cached value
            if let Some(cached) = d.get_cached() {
                return Ok(cached);
            }

            // Get the thunk and evaluate it
            if let Some(thunk) = d.get_thunk() {
                let result = apply(&thunk, &[])?;
                d.set_realized(result.clone());
                Ok(result)
            } else {
                // Should not happen - if not cached, must have thunk
                Err(Error::syntax("force", "delay in invalid state"))
            }
        }
        // Non-delay values are returned unchanged
        other => Ok(other.clone()),
    }
}

/// (time expr) - Evaluate expr, print elapsed time, return result
fn eval_time(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("time", "requires exactly 1 expression"));
    }

    use std::time::Instant;

    let start = Instant::now();
    let result = eval(&args[0], env)?;
    let elapsed = start.elapsed();

    // Print to stderr like Clojure
    eprintln!(
        "\"Elapsed time: {:.6} msecs\"",
        elapsed.as_secs_f64() * 1000.0
    );

    Ok(result)
}

/// (eval form) - Evaluate a form
fn eval_eval(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("eval", "requires exactly 1 argument"));
    }

    // First evaluate the argument to get the form to eval
    let form = eval(&args[0], env)?;

    // Then evaluate that form
    eval(&form, env)
}

/// (load-string s) - Read and evaluate all forms in string, return last result
fn eval_load_string(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("load-string", "requires exactly 1 argument"));
    }

    // Evaluate the argument to get the string
    let s = eval(&args[0], env)?;
    let code = match &s {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "load-string",
                "string",
                other.type_name(),
            ));
        }
    };

    // Parse and evaluate all forms
    let mut parser =
        klujur_parser::Parser::new(code).map_err(|e| Error::EvalError(format!("{:?}", e)))?;

    let mut result = KlujurVal::Nil;
    while let Some(form) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("{:?}", e)))?
    {
        result = eval(&form, env)?;
    }

    Ok(result)
}

/// (load-file path) - Load and evaluate all forms in a file, return last result
fn eval_load_file(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("load-file", "requires exactly 1 argument"));
    }

    // Evaluate the argument to get the path
    let path_val = eval(&args[0], env)?;
    let path = match &path_val {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "load-file",
                "string",
                other.type_name(),
            ));
        }
    };

    // Read the file contents
    let content = std::fs::read_to_string(path)
        .map_err(|e| Error::EvalError(format!("Could not read file '{}': {}", path, e)))?;

    // Parse and evaluate all forms
    let mut parser =
        klujur_parser::Parser::new(&content).map_err(|e| Error::EvalError(format!("{:?}", e)))?;

    let mut result = KlujurVal::Nil;
    while let Some(form) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("{:?}", e)))?
    {
        result = eval(&form, env)?;
    }

    Ok(result)
}

// ============================================================================
// Destructuring
// ============================================================================

/// Result of destructuring: a list of (symbol, value) bindings
type Bindings = Vec<(Symbol, KlujurVal)>;

/// Destructure a binding pattern against a value, returning bindings.
/// Supports:
/// - Symbols: `x` binds directly
/// - Vectors: `[a b c]`, `[a & rest]`, `[a :as all]`
/// - Maps: `{:keys [a b]}`, `{a :a}`, `{:or {a 1}}`, `{:as m}`
fn destructure(pattern: &KlujurVal, value: &KlujurVal) -> Result<Bindings> {
    match pattern {
        // Simple symbol binding
        KlujurVal::Symbol(sym, _) => Ok(vec![(sym.clone(), value.clone())]),

        // Sequential destructuring
        KlujurVal::Vector(patterns, _) => {
            let patterns_vec: Vec<KlujurVal> = patterns.iter().cloned().collect();
            destructure_sequential(&patterns_vec, value)
        }

        // Associative destructuring
        KlujurVal::Map(map, _) => destructure_associative(map, value),

        other => Err(Error::syntax(
            "destructure",
            format!(
                "binding pattern must be a symbol, vector, or map, got {}",
                other.type_name()
            ),
        )),
    }
}

/// Destructure a sequential pattern (vector) against a value.
/// Supports: [a b c], [a & rest], [a :as all], [_ b c] (ignore with _)
fn destructure_sequential(patterns: &[KlujurVal], value: &KlujurVal) -> Result<Bindings> {
    let mut bindings = Vec::new();

    // Convert value to a sequence
    let items = value_to_seq(value)?;

    let mut pattern_idx = 0;
    let mut value_idx = 0;

    while pattern_idx < patterns.len() {
        let pat = &patterns[pattern_idx];

        // Check for special keywords
        if let KlujurVal::Keyword(kw) = pat
            && kw.name() == "as"
        {
            // :as binding - bind the entire value
            if pattern_idx + 1 >= patterns.len() {
                return Err(Error::syntax(
                    "destructure",
                    ":as must be followed by a symbol",
                ));
            }
            let as_sym = match &patterns[pattern_idx + 1] {
                KlujurVal::Symbol(s, _) => s.clone(),
                other => {
                    return Err(Error::syntax(
                        "destructure",
                        format!(
                            ":as must be followed by a symbol, got {}",
                            other.type_name()
                        ),
                    ));
                }
            };
            bindings.push((as_sym, value.clone()));
            pattern_idx += 2;
            continue;
        }

        // Check for & rest
        if let KlujurVal::Symbol(sym, _) = pat {
            if sym.name() == "&" {
                // Rest binding
                if pattern_idx + 1 >= patterns.len() {
                    return Err(Error::syntax(
                        "destructure",
                        "& must be followed by a binding",
                    ));
                }
                let rest_value = if value_idx < items.len() {
                    KlujurVal::list(items[value_idx..].to_vec())
                } else {
                    KlujurVal::Nil
                };
                // Recursively destructure the rest pattern
                let rest_bindings = destructure(&patterns[pattern_idx + 1], &rest_value)?;
                bindings.extend(rest_bindings);
                pattern_idx += 2;
                // Skip to end - & consumes the rest
                value_idx = items.len();
                continue;
            }

            // Ignore binding with _
            if sym.name() == "_" {
                pattern_idx += 1;
                value_idx += 1;
                continue;
            }
        }

        // Regular binding - get value at current index (or nil if out of bounds)
        let item_value = if value_idx < items.len() {
            items[value_idx].clone()
        } else {
            KlujurVal::Nil
        };

        // Recursively destructure (handles nested patterns)
        let item_bindings = destructure(pat, &item_value)?;
        bindings.extend(item_bindings);

        pattern_idx += 1;
        value_idx += 1;
    }

    Ok(bindings)
}

/// Destructure an associative pattern (map) against a value.
/// Supports: {:keys [a b]}, {:strs [a b]}, {:syms [a b]}, {a :a}, {:or {...}}, {:as m}
#[allow(clippy::mutable_key_type)]
fn destructure_associative(
    patterns: &OrdMap<KlujurVal, KlujurVal>,
    value: &KlujurVal,
) -> Result<Bindings> {
    use klujur_parser::Keyword;

    let mut bindings = Vec::new();
    let mut defaults: Option<&OrdMap<KlujurVal, KlujurVal>> = None;

    // First pass: find :or defaults
    let or_key = KlujurVal::keyword(Keyword::new("or"));
    if let Some(or_val) = patterns.get(&or_key) {
        if let KlujurVal::Map(defaults_map, _) = or_val {
            defaults = Some(defaults_map);
        } else {
            return Err(Error::syntax(
                "destructure",
                format!(":or value must be a map, got {}", or_val.type_name()),
            ));
        }
    }

    // Get the value as a map (if it's not, we'll get nil for all lookups)
    let value_map: Option<&OrdMap<KlujurVal, KlujurVal>> = match value {
        KlujurVal::Map(m, _) => Some(m),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::syntax(
                "destructure",
                format!("cannot destructure {} as a map", other.type_name()),
            ));
        }
    };

    // Process each pattern entry
    for (pat_key, pat_val) in patterns.iter() {
        // Skip :or - already processed
        if *pat_key == or_key {
            continue;
        }

        // Check for special keywords
        if let KlujurVal::Keyword(kw) = pat_key {
            match kw.name() {
                "keys" => {
                    // {:keys [a b c]} - bind symbols to keyword lookups
                    let syms = extract_symbols(pat_val, ":keys")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::keyword(Keyword::new(sym.name()));
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "strs" => {
                    // {:strs [a b c]} - bind symbols to string lookups
                    let syms = extract_symbols(pat_val, ":strs")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::string(sym.name());
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "syms" => {
                    // {:syms [a b c]} - bind symbols to symbol lookups
                    let syms = extract_symbols(pat_val, ":syms")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::symbol(Symbol::new(sym.name()));
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "as" => {
                    // {:as m} - bind entire map
                    let as_sym = match pat_val {
                        KlujurVal::Symbol(s, _) => s.clone(),
                        other => {
                            return Err(Error::syntax(
                                "destructure",
                                format!(
                                    ":as must be followed by a symbol, got {}",
                                    other.type_name()
                                ),
                            ));
                        }
                    };
                    bindings.push((as_sym, value.clone()));
                    continue;
                }
                _ => {}
            }
        }

        // Regular map destructuring: {local-name lookup-key}
        // The key is the local binding, the value is what to look up
        let local_sym = match pat_key {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "destructure",
                    format!(
                        "map destructuring key must be a symbol, got {}",
                        other.type_name()
                    ),
                ));
            }
        };

        // Look up the value using pat_val as the key
        let looked_up = value_map
            .and_then(|m| m.get(pat_val).cloned())
            .unwrap_or(KlujurVal::Nil);

        // Apply defaults if nil
        let final_val = if looked_up == KlujurVal::Nil {
            defaults
                .and_then(|d| d.get(&KlujurVal::symbol(local_sym.clone())).cloned())
                .unwrap_or(KlujurVal::Nil)
        } else {
            looked_up
        };

        // Bind the symbol to the value
        bindings.push((local_sym, final_val));
    }

    Ok(bindings)
}

/// Extract symbols from a vector for :keys/:strs/:syms
fn extract_symbols(val: &KlujurVal, context: &str) -> Result<Vec<Symbol>> {
    let items = match val {
        KlujurVal::Vector(v, _) => v,
        other => {
            return Err(Error::syntax(
                "destructure",
                format!("{} requires a vector, got {}", context, other.type_name()),
            ));
        }
    };

    items
        .iter()
        .map(|item| match item {
            KlujurVal::Symbol(s, _) => Ok(s.clone()),
            other => Err(Error::syntax(
                "destructure",
                format!(
                    "{} vector must contain symbols, got {}",
                    context,
                    other.type_name()
                ),
            )),
        })
        .collect()
}

/// Look up a key in a map with fallback to defaults
fn lookup_with_default(
    key: &KlujurVal,
    value_map: Option<&OrdMap<KlujurVal, KlujurVal>>,
    defaults: Option<&OrdMap<KlujurVal, KlujurVal>>,
    sym: &Symbol,
) -> KlujurVal {
    let looked_up = value_map.and_then(|m| m.get(key).cloned());
    match looked_up {
        Some(v) if v != KlujurVal::Nil => v,
        _ => defaults
            .and_then(|d| d.get(&KlujurVal::symbol(sym.clone())).cloned())
            .unwrap_or(KlujurVal::Nil),
    }
}

/// Convert a value to a sequence (Vec) for destructuring
fn value_to_seq(value: &KlujurVal) -> Result<Vec<KlujurVal>> {
    match value {
        KlujurVal::List(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Vector(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Nil => Ok(vec![]),
        KlujurVal::String(s) => {
            // Strings destructure to characters
            Ok(s.chars().map(KlujurVal::char).collect())
        }
        other => Err(Error::syntax(
            "destructure",
            format!("cannot destructure {} as a sequence", other.type_name()),
        )),
    }
}

// ============================================================================
// Function Application
// ============================================================================

/// Apply a function to arguments.
pub fn apply(func: &KlujurVal, args: &[KlujurVal]) -> Result<KlujurVal> {
    match func {
        KlujurVal::Fn(f) => apply_fn(f, args),
        KlujurVal::NativeFn(f) => apply_native(f, args),
        KlujurVal::Keyword(kw) => {
            // Keywords can be called as functions: (:key map) => (get map :key)
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named(format!("{}", kw), 1, args.len()));
            }
            match &args[0] {
                KlujurVal::Map(map, _) => {
                    let key = KlujurVal::Keyword(kw.clone());
                    Ok(map.get(&key).cloned().unwrap_or_else(|| {
                        if args.len() == 2 {
                            args[1].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    }))
                }
                KlujurVal::Record(r) => {
                    // Keywords work on records: (:name person)
                    Ok(r.get(kw).cloned().unwrap_or_else(|| {
                        if args.len() == 2 {
                            args[1].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    }))
                }
                _ => Ok(if args.len() == 2 {
                    args[1].clone()
                } else {
                    KlujurVal::Nil
                }),
            }
        }
        KlujurVal::Vector(vec, _) => {
            // Vectors can be called as functions: ([a b c] 1) => b
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named("vector", 1, args.len()));
            }
            match &args[0] {
                KlujurVal::Int(idx) => {
                    let i = *idx;
                    let idx_usize = i as usize;
                    if idx_usize < vec.len() {
                        Ok(vec[idx_usize].clone())
                    } else if args.len() == 2 {
                        Ok(args[1].clone())
                    } else {
                        Err(Error::IndexOutOfBounds {
                            index: i,
                            length: vec.len(),
                        })
                    }
                }
                _ => Err(Error::type_error_in(
                    "vector lookup",
                    "integer",
                    args[0].type_name(),
                )),
            }
        }
        KlujurVal::Map(map, _) => {
            // Maps can be called as functions: ({:a 1} :a) => 1
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named("map", 1, args.len()));
            }
            let key = &args[0];
            Ok(map.get(key).cloned().unwrap_or_else(|| {
                if args.len() == 2 {
                    args[1].clone()
                } else {
                    KlujurVal::Nil
                }
            }))
        }
        KlujurVal::Set(set, _) => {
            // Sets can be called as functions: (#{:a :b} :a) => :a (or nil)
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named("set", 1, args.len()));
            }
            let key = &args[0];
            if set.contains(key) {
                Ok(key.clone())
            } else if args.len() == 2 {
                Ok(args[1].clone())
            } else {
                Ok(KlujurVal::Nil)
            }
        }
        KlujurVal::Multimethod(mm) => {
            // 1. Call dispatch function with all args
            let dispatch_val = apply(&mm.dispatch_fn, args)?;

            // 2. Look up method for dispatch value (falls back to default)
            let method = mm.get_method(&dispatch_val).ok_or_else(|| {
                Error::EvalError(format!(
                    "No method in multimethod '{}' for dispatch value: {}",
                    mm.name, dispatch_val
                ))
            })?;

            // 3. Call method with original args
            apply(&method, args)
        }
        other => Err(Error::NotCallable(format!("{}", other))),
    }
}

/// Apply a user-defined function.
/// Supports destructuring patterns in parameters.
fn apply_fn(func: &KlujurFn, args: &[KlujurVal]) -> Result<KlujurVal> {
    // Find matching arity
    let arity = func.find_arity(args.len()).ok_or_else(|| {
        // Build error message showing available arities
        let arity_strs: Vec<String> = func
            .arities
            .iter()
            .map(|a| {
                if a.rest_param.is_some() {
                    format!("{}+", a.params.len())
                } else {
                    a.params.len().to_string()
                }
            })
            .collect();
        Error::EvalError(format!(
            "Wrong number of args ({}) passed to fn; expected {}",
            args.len(),
            arity_strs.join(" or ")
        ))
    })?;

    // Downcast the environment
    let captured_env = func
        .env
        .downcast_ref::<Env>()
        .expect("Function environment must be Env type");

    // Create function environment
    let fn_env = captured_env.child();

    // Bind function name for self-recursion if present
    if let Some(name) = &func.name {
        fn_env.define(name.clone(), KlujurVal::Fn(func.clone()));
    }

    // Check if we have destructuring patterns
    let has_patterns = !arity.param_patterns.is_empty();

    if has_patterns {
        // Bind parameters with destructuring
        for (i, (param, arg)) in arity.params.iter().zip(args.iter()).enumerate() {
            // First bind the gensym param
            fn_env.define(param.clone(), arg.clone());

            // Then destructure the pattern
            let pattern = &arity.param_patterns[i];
            let binds = destructure(pattern, arg)?;
            for (sym, val) in binds {
                fn_env.define(sym, val);
            }
        }

        // Bind rest parameter with destructuring if present
        if let Some(rest) = &arity.rest_param {
            let rest_args: Vec<KlujurVal> = args[arity.params.len()..].to_vec();
            let rest_val = KlujurVal::list(rest_args);
            fn_env.define(rest.clone(), rest_val.clone());

            // Destructure rest pattern if present
            if let Some(rest_pattern) = &arity.rest_pattern {
                let binds = destructure(rest_pattern, &rest_val)?;
                for (sym, val) in binds {
                    fn_env.define(sym, val);
                }
            }
        }
    } else {
        // Simple parameter binding (no destructuring)
        for (param, arg) in arity.params.iter().zip(args.iter()) {
            fn_env.define(param.clone(), arg.clone());
        }

        // Bind rest parameter if present
        if let Some(rest) = &arity.rest_param {
            let rest_args: Vec<KlujurVal> = args[arity.params.len()..].to_vec();
            fn_env.define(rest.clone(), KlujurVal::list(rest_args));
        }
    }

    // Evaluate body
    let mut result = KlujurVal::Nil;
    for expr in &arity.body {
        result = eval(expr, &fn_env)?;
    }
    Ok(result)
}

/// Apply a native function.
fn apply_native(func: &KlujurNativeFn, args: &[KlujurVal]) -> Result<KlujurVal> {
    // Downcast the function
    let f = func
        .func()
        .downcast_ref::<Rc<NativeFnImpl>>()
        .expect("Native function must have correct type");
    f(args)
}

// ============================================================================
// Helper for creating native functions
// ============================================================================

/// Create a native function value.
pub fn make_native_fn(
    name: &'static str,
    func: impl Fn(&[KlujurVal]) -> Result<KlujurVal> + 'static,
) -> KlujurNativeFn {
    let func_rc: Rc<NativeFnImpl> = Rc::new(func);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    KlujurNativeFn::new(name, func_any)
}

// ============================================================================
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
}
