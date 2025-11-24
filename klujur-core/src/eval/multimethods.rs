// klujur-core - Multimethod special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Multimethod special forms: defmulti, defmethod, derive, underive, isa?, parents, ancestors, descendants

use std::any::Any;
use std::cell::RefCell;
use std::rc::Rc;

use klujur_parser::{FnArity, KlujurFn, KlujurHierarchy, KlujurMultimethod, KlujurVal};

use crate::bindings::deref_var;
use crate::env::Env;
use crate::error::{AritySpec, Error, Result};

use super::{eval, parse_fn_arity};

// ============================================================================
// Multimethods
// ============================================================================

/// (defmulti name dispatch-fn & options) - define a multimethod
/// Options:
///   :hierarchy h - use hierarchy h for isa? dispatch (defaults to global hierarchy)
pub(crate) fn eval_defmulti(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
                // Handle both direct hierarchy and var reference (#'my-h)
                let hierarchy_val = match &h_val {
                    KlujurVal::Var(v) => deref_var(v),
                    other => other.clone(),
                };
                match hierarchy_val {
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
pub(crate) fn eval_defmethod(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        .ok_or_else(|| Error::UndefinedSymbol(mm_name.clone()))?;

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
pub(crate) fn eval_derive(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: n,
            name: Some("derive".to_string()),
        }),
    }
}

/// (underive child parent) - removes a parent/child relationship from the global hierarchy
/// (underive h child parent) - removes a parent/child relationship from hierarchy h
pub(crate) fn eval_underive(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: n,
            name: Some("underive".to_string()),
        }),
    }
}

/// (isa? child parent) - returns true if child derives from parent (using global hierarchy)
/// (isa? h child parent) - returns true if child derives from parent (using hierarchy h)
pub(crate) fn eval_isa(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: n,
            name: Some("isa?".to_string()),
        }),
    }
}

/// (parents child) - returns the immediate parents of child (using global hierarchy)
/// (parents h child) - returns the immediate parents of child (using hierarchy h)
pub(crate) fn eval_parents(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("parents".to_string()),
        }),
    }
}

/// (ancestors child) - returns all ancestors of child (using global hierarchy)
/// (ancestors h child) - returns all ancestors of child (using hierarchy h)
pub(crate) fn eval_ancestors(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("ancestors".to_string()),
        }),
    }
}

/// (descendants parent) - returns all descendants of parent (using global hierarchy)
/// (descendants h parent) - returns all descendants of parent (using hierarchy h)
pub(crate) fn eval_descendants(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
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
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("descendants".to_string()),
        }),
    }
}
