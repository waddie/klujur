// klujur-core - Transducer built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Transducer operations: reduced, reduced?, unreduced, ensure-reduced, transduce
//! Volatile operations: volatile!, volatile?, vreset!, vswap!

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};
use crate::eval::apply;

use super::to_seq;

// ============================================================================
// Reduced Type
// ============================================================================

/// (reduced x) - Wrap x in a Reduced marker for early termination in transducers
pub(crate) fn builtin_reduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("reduced".into()),
        });
    }
    Ok(KlujurVal::reduced(args[0].clone()))
}

/// (reduced? x) - Returns true if x is a Reduced value
pub(crate) fn builtin_reduced_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("reduced?".into()),
        });
    }
    Ok(KlujurVal::Bool(matches!(&args[0], KlujurVal::Reduced(_))))
}

/// (unreduced x) - If x is Reduced, unwrap it; otherwise return x unchanged
pub(crate) fn builtin_unreduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("unreduced".into()),
        });
    }
    match &args[0] {
        KlujurVal::Reduced(v) => Ok((**v).clone()),
        v => Ok(v.clone()),
    }
}

/// (ensure-reduced x) - If x is not already Reduced, wrap it; otherwise return x
pub(crate) fn builtin_ensure_reduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("ensure-reduced".into()),
        });
    }
    match &args[0] {
        KlujurVal::Reduced(_) => Ok(args[0].clone()),
        v => Ok(KlujurVal::reduced(v.clone())),
    }
}

// ============================================================================
// Volatiles - Lightweight Mutable State for Transducers
// ============================================================================

/// (volatile! x) - Create a volatile with initial value x
pub(crate) fn builtin_volatile(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("volatile!".into()),
        });
    }
    Ok(KlujurVal::volatile(args[0].clone()))
}

/// (volatile? x) - Returns true if x is a Volatile
pub(crate) fn builtin_volatile_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("volatile?".into()),
        });
    }
    Ok(KlujurVal::Bool(matches!(&args[0], KlujurVal::Volatile(_))))
}

/// (vreset! vol newval) - Set volatile's value to newval, returns newval
pub(crate) fn builtin_vreset(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(2),
            got: args.len(),
            name: Some("vreset!".into()),
        });
    }
    match &args[0] {
        KlujurVal::Volatile(v) => Ok(v.reset(args[1].clone())),
        other => Err(Error::type_error_in(
            "vreset!",
            "volatile",
            other.type_name(),
        )),
    }
}

/// (vswap! vol f & args) - Atomically swaps value of volatile to (apply f current-value args)
pub(crate) fn builtin_vswap(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::AtLeast(2),
            got: args.len(),
            name: Some("vswap!".into()),
        });
    }
    let vol = match &args[0] {
        KlujurVal::Volatile(v) => v,
        other => {
            return Err(Error::type_error_in(
                "vswap!",
                "volatile",
                other.type_name(),
            ));
        }
    };
    let f = &args[1];

    // Get current value
    let old_val = vol.deref();

    // Build args: [old-val, ...extra-args]
    let mut call_args = vec![old_val];
    call_args.extend(args[2..].iter().cloned());

    // Apply f
    let new_val = apply(f, &call_args)?;

    // Set and return
    Ok(vol.reset(new_val))
}

// ============================================================================
// Transducer Execution
// ============================================================================

/// (transduce xform f coll)
/// (transduce xform f init coll)
/// Reduce with transducer. Applies xform to f to get transformed reducing function,
/// then reduces coll with it. Handles early termination via Reduced.
pub(crate) fn builtin_transduce(args: &[KlujurVal]) -> Result<KlujurVal> {
    let (xform, f, init, coll) = match args.len() {
        3 => {
            // (transduce xform f coll) - get init by calling (f)
            let xform = &args[0];
            let f = &args[1];
            let coll = &args[2];
            let init = apply(f, &[])?;
            (xform, f, init, coll)
        }
        4 => {
            // (transduce xform f init coll)
            (&args[0], &args[1], args[2].clone(), &args[3])
        }
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(3, 4),
                got: args.len(),
                name: Some("transduce".into()),
            });
        }
    };

    // Apply transducer to get transformed reducing function
    // xf = (xform f)
    let xf = apply(xform, std::slice::from_ref(f))?;

    // Get sequence from collection
    let items = to_seq(coll)?;

    // Reduce with transformed function
    let mut result = init;
    for item in items {
        result = apply(&xf, &[result, item])?;
        // Check for early termination with Reduced
        if let KlujurVal::Reduced(v) = result {
            result = (*v).clone();
            break;
        }
    }

    // Call completion arity: (xf result)
    apply(&xf, &[result])
}
