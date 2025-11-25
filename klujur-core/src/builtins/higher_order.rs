// klujur-core - Higher-order built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Higher-order functions: apply, map, filter, reduce, comp, partial, etc.

use std::any::Any;
use std::rc::Rc;

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};
use crate::eval::{NativeFnImpl, apply};

use super::{seq_iter, to_seq};

// ============================================================================
// Core Higher-Order Functions
// ============================================================================

/// (apply f args) or (apply f a b c args) - apply function to arguments
pub(crate) fn builtin_apply(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let func = &args[0];

    // Collect all arguments: intermediate args + spread of final seq
    let mut all_args = Vec::new();

    // Add intermediate arguments (everything except first and last)
    for arg in &args[1..args.len() - 1] {
        all_args.push(arg.clone());
    }

    // Spread the last argument (must be a seqable)
    let last = &args[args.len() - 1];
    match last {
        KlujurVal::List(items, _) => all_args.extend(items.iter().cloned()),
        KlujurVal::Vector(items, _) => all_args.extend(items.iter().cloned()),
        KlujurVal::Nil => {} // nil as empty seq
        KlujurVal::LazySeq(_) => {
            // Force the lazy seq and spread its elements
            let items = to_seq(last)?;
            all_args.extend(items);
        }
        other => {
            return Err(Error::type_error_in("apply", "seqable", other.type_name()));
        }
    }

    // Call the function with the collected arguments
    apply(func, &all_args)
}

/// (map f coll) - apply f to each element, return lazy seq
pub(crate) fn builtin_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let func = &args[0];

    if args.len() == 2 {
        // Single collection - use streaming iterator
        let mut result = Vec::new();
        for item in seq_iter(&args[1])? {
            result.push(apply(func, &[item?])?);
        }
        Ok(KlujurVal::list(result))
    } else {
        // Multiple collections - zip them (still needs to_seq for indexing)
        let colls: Result<Vec<Vec<KlujurVal>>> = args[1..].iter().map(to_seq).collect();
        let colls = colls?;

        // Find minimum length
        let min_len = colls.iter().map(|c| c.len()).min().unwrap_or(0);

        let mut result = Vec::with_capacity(min_len);
        for i in 0..min_len {
            let call_args: Vec<KlujurVal> = colls.iter().map(|c| c[i].clone()).collect();
            result.push(apply(func, &call_args)?);
        }
        Ok(KlujurVal::list(result))
    }
}

/// (filter pred coll) - return elements where (pred elem) is truthy
pub(crate) fn builtin_filter(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("filter", 2, args.len()));
    }

    let pred = &args[0];
    let mut result = Vec::new();
    for item in seq_iter(&args[1])? {
        let item = item?;
        let test = apply(pred, std::slice::from_ref(&item))?;
        if test.is_truthy() {
            result.push(item);
        }
    }
    Ok(KlujurVal::list(result))
}

/// (remove pred coll) - return elements where (pred elem) is falsy
pub(crate) fn builtin_remove(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove", 2, args.len()));
    }

    let pred = &args[0];
    let mut result = Vec::new();
    for item in seq_iter(&args[1])? {
        let item = item?;
        let test = apply(pred, std::slice::from_ref(&item))?;
        if !test.is_truthy() {
            result.push(item);
        }
    }
    Ok(KlujurVal::list(result))
}

/// (reduce f init coll) or (reduce f coll) - reduce collection
pub(crate) fn builtin_reduce(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("reduce".into()),
        });
    }

    let func = &args[0];

    if args.len() == 2 {
        // No initial value - use first element
        let mut iter = seq_iter(&args[1])?;
        let mut acc = match iter.next() {
            None => return apply(func, &[]), // (reduce f []) => (f)
            Some(first) => first?,
        };
        for item in iter {
            acc = apply(func, &[acc, item?])?;
            // Check for early termination with Reduced
            if let KlujurVal::Reduced(v) = acc {
                return Ok((*v).clone());
            }
        }
        Ok(acc)
    } else {
        // With initial value
        let mut acc = args[1].clone();
        for item in seq_iter(&args[2])? {
            acc = apply(func, &[acc, item?])?;
            // Check for early termination with Reduced
            if let KlujurVal::Reduced(v) = acc {
                return Ok((*v).clone());
            }
        }
        Ok(acc)
    }
}

// ============================================================================
// Function Composition
// ============================================================================

/// (comp f g ...) - compose functions right-to-left
pub(crate) fn builtin_comp(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        // (comp) returns identity
        return Ok(KlujurVal::NativeFn(crate::eval::make_native_fn(
            "comp",
            builtin_identity,
        )));
    }

    // Store functions in reverse order for right-to-left composition
    let funcs: Vec<KlujurVal> = args.iter().rev().cloned().collect();
    let funcs_rc = Rc::new(funcs);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut result = apply(&funcs_rc[0], call_args)?;
        for f in funcs_rc.iter().skip(1) {
            result = apply(f, &[result])?;
        }
        Ok(result)
    };

    let func_rc: Rc<NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "comp", func_any,
    )))
}

/// (partial f arg1 arg2 ...) - partially apply function
pub(crate) fn builtin_partial(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let func = args[0].clone();
    let bound_args: Vec<KlujurVal> = args[1..].to_vec();

    let func_rc = Rc::new(func);
    let bound_rc = Rc::new(bound_args);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut all_args = (*bound_rc).clone();
        all_args.extend(call_args.iter().cloned());
        apply(&func_rc, &all_args)
    };

    let func_rc: Rc<NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "partial", func_any,
    )))
}

/// (constantly x) - return a function that always returns x
pub(crate) fn builtin_constantly(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("constantly", 1, args.len()));
    }

    let value = args[0].clone();
    let value_rc = Rc::new(value);

    let closure = move |_call_args: &[KlujurVal]| -> Result<KlujurVal> { Ok((*value_rc).clone()) };

    let func_rc: Rc<NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "constantly",
        func_any,
    )))
}

// ============================================================================
// Predicates over Collections
// ============================================================================

/// (every? pred coll) - true if (pred x) is truthy for all x
pub(crate) fn builtin_every_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("every?", 2, args.len()));
    }

    let pred = &args[0];
    for item in seq_iter(&args[1])? {
        let test = apply(pred, &[item?])?;
        if !test.is_truthy() {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (some pred coll) - return first truthy result of (pred x), or nil
pub(crate) fn builtin_some(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("some", 2, args.len()));
    }

    let pred = &args[0];
    for item in seq_iter(&args[1])? {
        let test = apply(pred, &[item?])?;
        if test.is_truthy() {
            return Ok(test);
        }
    }
    Ok(KlujurVal::Nil)
}

/// (not-any? pred coll) - true if (pred x) is falsy for all x
pub(crate) fn builtin_not_any_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("not-any?", 2, args.len()));
    }

    let pred = &args[0];
    for item in seq_iter(&args[1])? {
        let test = apply(pred, &[item?])?;
        if test.is_truthy() {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (not-every? pred coll) - true if (pred x) is falsy for any x
pub(crate) fn builtin_not_every_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("not-every?", 2, args.len()));
    }

    let pred = &args[0];
    for item in seq_iter(&args[1])? {
        let test = apply(pred, &[item?])?;
        if !test.is_truthy() {
            return Ok(KlujurVal::bool(true));
        }
    }
    Ok(KlujurVal::bool(false))
}

// ============================================================================
// Utility
// ============================================================================

/// (identity x) - return x unchanged
pub(crate) fn builtin_identity(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("identity", 1, args.len()));
    }
    Ok(args[0].clone())
}
