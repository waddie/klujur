// klujur-core - Function application
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Function application for Klujur.

use std::any::Any;
use std::rc::Rc;

use klujur_parser::{KlujurFn, KlujurNativeFn, KlujurVal};

use crate::builtins::collection_constructors::{sorted_map_by_get, sorted_set_by_contains};

use super::destructuring::destructure;
use super::eval;
use crate::env::Env;
use crate::error::{Error, Result};

/// Type alias for native function signature.
pub type NativeFnImpl = dyn Fn(&[KlujurVal]) -> Result<KlujurVal>;

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
                    // Check for negative index before casting to usize
                    if i < 0 || i as usize >= vec.len() {
                        if args.len() == 2 {
                            Ok(args[1].clone())
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: i,
                                length: vec.len(),
                            })
                        }
                    } else {
                        Ok(vec[i as usize].clone())
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
        KlujurVal::SortedMapBy(sm) => {
            // Sorted maps can be called as functions: (sm key) => value
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named("sorted-map-by", 1, args.len()));
            }
            let key = &args[0];
            match sorted_map_by_get(sm, key)? {
                Some(val) => Ok(val),
                None => {
                    if args.len() == 2 {
                        Ok(args[1].clone())
                    } else {
                        Ok(KlujurVal::Nil)
                    }
                }
            }
        }
        KlujurVal::SortedSetBy(ss) => {
            // Sorted sets can be called as functions: (ss key) => key (or nil)
            if args.len() != 1 && args.len() != 2 {
                return Err(Error::arity_named("sorted-set-by", 1, args.len()));
            }
            let key = &args[0];
            if sorted_set_by_contains(ss, key)? {
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
pub(crate) fn apply_fn(func: &KlujurFn, args: &[KlujurVal]) -> Result<KlujurVal> {
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
        .ok_or_else(|| Error::Internal("Function environment has invalid type".into()))?;

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
pub(crate) fn apply_native(func: &KlujurNativeFn, args: &[KlujurVal]) -> Result<KlujurVal> {
    // Downcast the function
    let f = func
        .func()
        .downcast_ref::<Rc<NativeFnImpl>>()
        .ok_or_else(|| Error::Internal("Native function has invalid type".into()))?;
    f(args)
}

/// Create a native function value.
pub fn make_native_fn(
    name: &'static str,
    func: impl Fn(&[KlujurVal]) -> Result<KlujurVal> + 'static,
) -> KlujurNativeFn {
    let func_rc: Rc<NativeFnImpl> = Rc::new(func);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    KlujurNativeFn::new(name, func_any)
}
