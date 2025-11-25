// klujur-core - Var and dynamic binding built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Var operations: var?, deref, alter-var-root
//! Dynamic binding operations: bound?, thread-bound?, var-get, var-set

use klujur_parser::KlujurVal;

use crate::bindings::{deref_var, has_thread_binding, set_thread_binding};
use crate::error::{Error, Result};
use crate::eval::apply;

// ============================================================================
// Vars
// ============================================================================

/// (var? x) - true if x is a Var
pub(crate) fn builtin_var_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("var?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(&args[0], KlujurVal::Var(_))))
}

/// (deref var) - get the value of a Var (also works with @var syntax when implemented)
pub(crate) fn builtin_deref(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("deref", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(v.deref()),
        KlujurVal::Atom(a) => Ok(a.deref()),
        KlujurVal::Delay(d) => {
            // If already realized, return cached value
            if let Some(val) = d.get_cached() {
                Ok(val)
            } else {
                // Deref on unrealized delay requires special form handling
                Err(Error::syntax(
                    "deref",
                    "deref on unrealized delay must be called directly (use @delay or force)",
                ))
            }
        }
        KlujurVal::Volatile(v) => Ok(v.deref()),
        other => Err(Error::type_error(
            "Var, Atom, Delay, or Volatile",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Dynamic Bindings
// ============================================================================

/// (bound? var) - check if a var has a value (root or thread-local)
pub(crate) fn builtin_bound_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("bound?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(_) => {
            // In our implementation, all vars have a root value when created
            Ok(KlujurVal::bool(true))
        }
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (thread-bound? var) - check if a var has a thread-local binding
pub(crate) fn builtin_thread_bound_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("thread-bound?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(KlujurVal::bool(has_thread_binding(v))),
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (var-get var) - get the value of a var (checking thread-local bindings)
pub(crate) fn builtin_var_get(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("var-get", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(deref_var(v)),
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (var-set var val) - set the value of a var in thread-local context
pub(crate) fn builtin_var_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("var-set", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => {
            if !v.is_dynamic() {
                return Err(Error::EvalError(format!(
                    "can't set non-dynamic var: {}",
                    v.qualified_name()
                )));
            }
            let val = args[1].clone();
            if set_thread_binding(v, val.clone()) {
                Ok(val)
            } else {
                Err(Error::EvalError(format!(
                    "can't set {} outside of binding context",
                    v.qualified_name()
                )))
            }
        }
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (alter-var-root var f & args) - atomically alter the root binding of a var
/// Applies f to the current root value and any optional args, then sets the result
/// as the new root value. Returns the new value.
pub(crate) fn builtin_alter_var_root(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    match &args[0] {
        KlujurVal::Var(v) => {
            let f = &args[1];
            let current = v.deref();

            // Build args: current value + any additional args
            let mut call_args = vec![current];
            call_args.extend(args[2..].iter().cloned());

            // Apply the function
            let new_val = apply(f, &call_args)?;

            // Set the new root value
            v.set_root(new_val.clone());

            Ok(new_val)
        }
        other => Err(Error::type_error("Var", other.type_name())),
    }
}
