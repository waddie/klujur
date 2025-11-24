// klujur-core - Multimethod and Hierarchy built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Multimethod operations: methods, get-method, remove-method, prefer-method
//! Hierarchy operations: make-hierarchy, isa?, parents, ancestors, descendants

use std::cell::RefCell;
use std::rc::Rc;

use klujur_parser::{KlujurHierarchy, KlujurVal, OrdMap};

use crate::error::{AritySpec, Error, Result};

// ============================================================================
// Multimethod Functions
// ============================================================================

/// (methods multimethod) - Returns a map of dispatch value -> method function
pub(crate) fn builtin_methods(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("methods", 1, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m,
        other => {
            return Err(Error::type_error_in(
                "methods",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    // Convert HashMap to OrdMap for consistent ordering
    let methods_map: OrdMap<KlujurVal, KlujurVal> = mm.get_methods().into_iter().collect();
    Ok(KlujurVal::Map(methods_map, None))
}

/// (get-method multimethod dispatch-val) - Returns the method for dispatch-val, or nil
pub(crate) fn builtin_get_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("get-method", 2, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m,
        other => {
            return Err(Error::type_error_in(
                "get-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    match mm.get_method(&args[1]) {
        Some(method) => Ok(method),
        None => Ok(KlujurVal::Nil),
    }
}

/// (remove-method multimethod dispatch-val) - Removes the method for dispatch-val
pub(crate) fn builtin_remove_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove-method", 2, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "remove-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    mm.remove_method(&args[1]);
    Ok(KlujurVal::Multimethod(mm))
}

/// (prefer-method multimethod preferred-val other-val) - Set preference for ambiguous dispatch
pub(crate) fn builtin_prefer_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("prefer-method", 3, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "prefer-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    mm.prefer_method(args[1].clone(), args[2].clone());
    Ok(KlujurVal::Multimethod(mm))
}

/// (prefers multimethod) - Returns a map of dispatch-val -> #{other-vals...} preferences
pub(crate) fn builtin_prefers(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("prefers", 1, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m,
        other => {
            return Err(Error::type_error_in(
                "prefers",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    // Convert HashMap<KlujurVal, OrdSet<KlujurVal>> to OrdMap<KlujurVal, KlujurVal>
    let prefers = mm.get_prefers();
    let result: OrdMap<KlujurVal, KlujurVal> = prefers
        .into_iter()
        .map(|(k, v)| (k, KlujurVal::Set(v, None)))
        .collect();
    Ok(KlujurVal::Map(result, None))
}

/// (remove-all-methods multimethod) - Removes all methods from the multimethod
pub(crate) fn builtin_remove_all_methods(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("remove-all-methods", 1, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "remove-all-methods",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    mm.clear_methods();
    Ok(KlujurVal::Multimethod(mm))
}

// ============================================================================
// Hierarchy Functions
// ============================================================================

/// (make-hierarchy) - Creates a new, independent, hierarchy
pub(crate) fn builtin_make_hierarchy(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("make-hierarchy", 0, args.len()));
    }
    Ok(KlujurVal::Hierarchy(Rc::new(RefCell::new(
        KlujurHierarchy::new(),
    ))))
}

/// (isa? child parent) - Returns true if child is derived from parent (using global hierarchy)
/// (isa? h child parent) - Returns true if child is derived from parent (using hierarchy h)
pub(crate) fn builtin_isa(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            // (isa? child parent) - uses global hierarchy
            // For now, just do equality check since we don't have access to global hierarchy here
            // The derive/isa? with global hierarchy requires special form access to env
            let child = &args[0];
            let parent = &args[1];
            // Without global hierarchy, isa? is just equality for non-hierarchy version
            // This will be enhanced when called from eval with env access
            Ok(KlujurVal::Bool(child == parent))
        }
        3 => {
            // (isa? h child parent) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in("isa?", "hierarchy", other.type_name()));
                }
            };
            let child = &args[1];
            let parent = &args[2];
            Ok(KlujurVal::Bool(h.borrow().isa(child, parent)))
        }
        n => Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: n,
            name: Some("isa?".to_string()),
        }),
    }
}

/// (parents child) - Returns the immediate parents of child (using global hierarchy)
/// (parents h child) - Returns the immediate parents of child (using hierarchy h)
pub(crate) fn builtin_parents(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (parents child) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (parents h child) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "parents",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let child = &args[1];
            let parents = h.borrow().parents(child);
            Ok(KlujurVal::set(parents.into_iter().collect()))
        }
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("parents".to_string()),
        }),
    }
}

/// (ancestors child) - Returns all ancestors of child (using global hierarchy)
/// (ancestors h child) - Returns all ancestors of child (using hierarchy h)
pub(crate) fn builtin_ancestors(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (ancestors child) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (ancestors h child) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "ancestors",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let child = &args[1];
            let ancestors = h.borrow().ancestors(child);
            Ok(KlujurVal::set(ancestors.into_iter().collect()))
        }
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("ancestors".to_string()),
        }),
    }
}

/// (descendants parent) - Returns all descendants of parent (using global hierarchy)
/// (descendants h parent) - Returns all descendants of parent (using hierarchy h)
pub(crate) fn builtin_descendants(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (descendants parent) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (descendants h parent) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "descendants",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let parent = &args[1];
            let descendants = h.borrow().descendants(parent);
            Ok(KlujurVal::set(descendants.into_iter().collect()))
        }
        n => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: n,
            name: Some("descendants".to_string()),
        }),
    }
}
