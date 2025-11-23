// klujur-core - Additional higher-order built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Additional higher-order functions: reduce-kv, juxt, complement, fnil, some-fn, every-pred

use std::any::Any;
use std::rc::Rc;

use klujur_parser::{KlujurNativeFn, KlujurVal};

use crate::error::{Error, Result};
use crate::eval::apply;

// ============================================================================
// Additional Higher-Order Functions
// ============================================================================

/// (reduce-kv f init coll) - reduce with key-value pairs
pub(crate) fn builtin_reduce_kv(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("reduce-kv", 3, args.len()));
    }
    let f = &args[0];
    let mut acc = args[1].clone();

    match &args[2] {
        KlujurVal::Map(map, _) => {
            for (k, v) in map.iter() {
                acc = apply(f, &[acc, k.clone(), v.clone()])?;
            }
            Ok(acc)
        }
        KlujurVal::Vector(items, _) => {
            for (i, v) in items.iter().enumerate() {
                acc = apply(f, &[acc, KlujurVal::int(i as i64), v.clone()])?;
            }
            Ok(acc)
        }
        KlujurVal::Nil => Ok(acc),
        other => Err(Error::type_error_in(
            "reduce-kv",
            "map or vector",
            other.type_name(),
        )),
    }
}

/// (juxt f & fs) - returns fn applying each f, returning vector
pub(crate) fn builtin_juxt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let funcs: Vec<KlujurVal> = args.to_vec();
    let funcs_rc = Rc::new(funcs);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut results = Vec::with_capacity(funcs_rc.len());
        for f in funcs_rc.iter() {
            results.push(apply(f, call_args)?);
        }
        Ok(KlujurVal::vector(results))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(KlujurNativeFn::new("juxt", func_any)))
}

/// (complement f) - returns fn returning logical opposite
pub(crate) fn builtin_complement(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("complement", 1, args.len()));
    }

    let f = args[0].clone();
    let f_rc = Rc::new(f);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let result = apply(&f_rc, call_args)?;
        Ok(KlujurVal::bool(!result.is_truthy()))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(KlujurNativeFn::new(
        "complement",
        func_any,
    )))
}

/// (fnil f default & defaults) - wrap f to replace nil args with defaults
pub(crate) fn builtin_fnil(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let f = args[0].clone();
    let defaults: Vec<KlujurVal> = args[1..].to_vec();

    let f_rc = Rc::new(f);
    let defaults_rc = Rc::new(defaults);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut new_args: Vec<KlujurVal> = call_args.to_vec();
        for (i, default) in defaults_rc.iter().enumerate() {
            if i < new_args.len() && matches!(new_args[i], KlujurVal::Nil) {
                new_args[i] = default.clone();
            }
        }
        apply(&f_rc, &new_args)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(KlujurNativeFn::new("fnil", func_any)))
}

/// (some-fn p & ps) - returns fn returning first truthy predicate result
pub(crate) fn builtin_some_fn(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let preds: Vec<KlujurVal> = args.to_vec();
    let preds_rc = Rc::new(preds);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        for arg in call_args {
            for pred in preds_rc.iter() {
                let result = apply(pred, std::slice::from_ref(arg))?;
                if result.is_truthy() {
                    return Ok(result);
                }
            }
        }
        Ok(KlujurVal::Nil)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(KlujurNativeFn::new(
        "some-fn", func_any,
    )))
}

/// (every-pred p & ps) - returns fn returning true if all predicates true
pub(crate) fn builtin_every_pred(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let preds: Vec<KlujurVal> = args.to_vec();
    let preds_rc = Rc::new(preds);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        for arg in call_args {
            for pred in preds_rc.iter() {
                let result = apply(pred, std::slice::from_ref(arg))?;
                if !result.is_truthy() {
                    return Ok(KlujurVal::bool(false));
                }
            }
        }
        Ok(KlujurVal::bool(true))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(KlujurNativeFn::new(
        "every-pred",
        func_any,
    )))
}
