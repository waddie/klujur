// klujur-core - Dynamic binding special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Dynamic binding special forms: binding, set!, swap!, swap-vals!, delay, lazy-seq, force

use std::any::Any;
use std::rc::Rc;

use klujur_parser::{FnArity, KlujurFn, KlujurVal, KlujurVar};

use crate::bindings::{push_bindings, set_thread_binding};
use crate::env::Env;
use crate::error::{Error, Result};

use klujur_parser::KlujurAtom;

use super::{apply, eval, lookup_symbol};

// ============================================================================
// Atom Validation Helper
// ============================================================================

/// Validate a new value against an atom's validator, then set the value.
/// In Clojure, if the validator returns false or throws, an IllegalStateException is raised.
fn validate_and_set_atom(atom: &KlujurAtom, new_val: KlujurVal) -> Result<()> {
    if let Some(validator) = atom.get_validator() {
        let result = apply(&validator, std::slice::from_ref(&new_val))?;
        if !result.is_truthy() {
            return Err(Error::EvalError("Invalid reference state".to_string()));
        }
    }
    atom.set_value(new_val);
    Ok(())
}

// ============================================================================
// Dynamic Binding
// ============================================================================

/// (binding [var1 val1 var2 val2 ...] body...)
/// Establishes thread-local bindings for dynamic vars.
pub(crate) fn eval_binding(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
pub(crate) fn eval_set_bang(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
pub(crate) fn eval_swap(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
    validate_and_set_atom(atom, new_val.clone())?;

    Ok(new_val)
}

/// (swap-vals! atom f & args) - Like swap!, returns [old new]
pub(crate) fn eval_swap_vals(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
    validate_and_set_atom(atom, new_val.clone())?;

    Ok(KlujurVal::vector(vec![old_val, new_val]))
}

/// (reset! atom newval) - Set atom value, returns newval
pub(crate) fn eval_reset(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::syntax("reset!", "requires exactly 2 arguments"));
    }

    let atom_val = eval(&args[0], env)?;
    let atom = match &atom_val {
        KlujurVal::Atom(a) => a,
        other => {
            return Err(Error::type_error_in("reset!", "atom", other.type_name()));
        }
    };

    let new_val = eval(&args[1], env)?;
    validate_and_set_atom(atom, new_val.clone())?;

    Ok(new_val)
}

/// (reset-vals! atom newval) - Set atom value, returns [old new]
pub(crate) fn eval_reset_vals(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::syntax("reset-vals!", "requires exactly 2 arguments"));
    }

    let atom_val = eval(&args[0], env)?;
    let atom = match &atom_val {
        KlujurVal::Atom(a) => a,
        other => {
            return Err(Error::type_error_in(
                "reset-vals!",
                "atom",
                other.type_name(),
            ));
        }
    };

    let old_val = atom.deref();
    let new_val = eval(&args[1], env)?;
    validate_and_set_atom(atom, new_val.clone())?;

    Ok(KlujurVal::vector(vec![old_val, new_val]))
}

/// (delay & body) - Create a delay that will evaluate body on first deref
pub(crate) fn eval_delay(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("delay", "requires a body"));
    }

    // Wrap the body in a thunk (zero-arg function)
    // The thunk captures the environment so it can be evaluated later
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
pub(crate) fn eval_lazy_seq(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Wrap the body in a thunk (zero-arg function)
    // The thunk captures the environment so it can be evaluated later
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
pub(crate) fn eval_force(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
