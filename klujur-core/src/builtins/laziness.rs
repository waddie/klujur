// klujur-core - Laziness and memoization built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Delay operations: delay?, realized?, lazy-seq?, doall, dorun, force
//! Memoization: memoize

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use klujur_parser::{KlujurNativeFn, KlujurVal};

use crate::error::{Error, Result};

use super::{SeqResult, force_lazy_seq};

// ============================================================================
// Delays
// ============================================================================

/// (delay? x) - Returns true if x is a delay
pub(crate) fn builtin_delay_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("delay?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Delay(_))))
}

/// (realized? x) - Returns true if a lazy value has been realized
pub(crate) fn builtin_realized_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("realized?", 1, args.len()));
    }
    let realized = match &args[0] {
        KlujurVal::Delay(d) => d.is_realized(),
        KlujurVal::LazySeq(ls) => ls.is_realized(),
        // Non-lazy values are always "realized"
        _ => true,
    };
    Ok(KlujurVal::bool(realized))
}

/// (lazy-seq? x) - Returns true if x is a lazy sequence
pub(crate) fn builtin_lazy_seq_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("lazy-seq?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::LazySeq(_))))
}

/// (doall coll) or (doall n coll) - Force the lazy sequence and return it
/// With n, forces only the first n elements.
pub(crate) fn builtin_doall(args: &[KlujurVal]) -> Result<KlujurVal> {
    let (limit, coll) = match args.len() {
        1 => (None, args[0].clone()),
        2 => {
            let n = match &args[0] {
                KlujurVal::Int(n) if *n >= 0 => *n as usize,
                KlujurVal::Int(_) => {
                    return Err(Error::EvalError(
                        "doall: n must be non-negative".to_string(),
                    ));
                }
                other => return Err(Error::type_error_in("doall", "integer", other.type_name())),
            };
            (Some(n), args[1].clone())
        }
        _ => return Err(Error::arity_range("doall", 1, 2, args.len())),
    };

    let mut current = coll.clone();
    let mut count = 0usize;

    // Walk through the sequence, forcing each element
    loop {
        // Check limit
        if let Some(max) = limit
            && count >= max
        {
            break;
        }

        match current {
            KlujurVal::Nil => break,
            KlujurVal::List(ref items, _) if items.is_empty() => break,
            KlujurVal::List(ref items, _) => {
                if items.len() <= 1 {
                    break;
                }
                current = KlujurVal::list(items.iter().skip(1).cloned().collect());
                count += 1;
            }
            KlujurVal::LazySeq(ref ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => break,
                SeqResult::Cons(_, rest) => {
                    current = rest;
                    count += 1;
                }
            },
            _ => break,
        }
    }

    Ok(coll)
}

/// (dorun coll) or (dorun n coll) - Force the lazy sequence, return nil (for side effects)
/// With n, forces only the first n elements.
pub(crate) fn builtin_dorun(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 | 2 => {
            // Reuse doall logic but return nil
            builtin_doall(args)?;
            Ok(KlujurVal::Nil)
        }
        _ => Err(Error::arity_range("dorun", 1, 2, args.len())),
    }
}

// Note: force is implemented as a special form in eval/dynamic.rs
// It is not registered as a builtin because it needs to evaluate the thunk
// (which builtins cannot do).

// ============================================================================
// Memoization
// ============================================================================

/// A memoized wrapper around a function.
///
/// # Reference Cycle Limitation
///
/// If a memoized function returns a value that captures a reference to itself
/// (e.g., a recursive closure that is memoized), a reference cycle can form:
/// `MemoizedFn -> cache -> result -> closure -> MemoizedFn`. This cycle
/// prevents the `MemoizedFn` from being deallocated.
///
/// This is a known limitation. In practice, most memoized functions return
/// simple values (numbers, strings, collections) that don't capture closures,
/// so this is rarely an issue. If you need to memoize self-referential
/// functions, consider using a separate cache data structure.
struct MemoizedFn {
    /// The original function
    f: KlujurVal,
    /// Cache: args -> result
    cache: RefCell<HashMap<Vec<KlujurVal>, KlujurVal>>,
}

impl MemoizedFn {
    fn new(f: KlujurVal) -> Self {
        MemoizedFn {
            f,
            cache: RefCell::new(HashMap::new()),
        }
    }

    fn call(&self, args: &[KlujurVal]) -> Result<KlujurVal> {
        let key: Vec<KlujurVal> = args.to_vec();

        // Check cache first
        if let Some(cached) = self.cache.borrow().get(&key) {
            return Ok(cached.clone());
        }

        // Call the original function
        let result = crate::eval::apply(&self.f, args)?;

        // Cache the result
        self.cache.borrow_mut().insert(key, result.clone());

        Ok(result)
    }
}

/// (memoize f) - Returns a cached version of f
pub(crate) fn builtin_memoize(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;

    if args.len() != 1 {
        return Err(Error::arity_named("memoize", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Fn(_) | KlujurVal::NativeFn(_) => {
            // Create the memoized wrapper
            let memo = Rc::new(MemoizedFn::new(args[0].clone()));

            // Create a native function that calls the memoized wrapper
            let closure =
                move |call_args: &[KlujurVal]| -> Result<KlujurVal> { memo.call(call_args) };

            // Double Rc wrapping required for native functions
            let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
            let func_any: Rc<dyn Any> = Rc::new(func_rc);
            Ok(KlujurVal::NativeFn(KlujurNativeFn::new(
                "memoized-fn",
                func_any,
            )))
        }
        other => Err(Error::type_error_in(
            "memoize",
            "function",
            other.type_name(),
        )),
    }
}
