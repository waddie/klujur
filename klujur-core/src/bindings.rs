// klujur-core - Dynamic binding frame management
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Thread-local binding frames for dynamic vars.
//!
//! This module provides the infrastructure for Clojure-style dynamic binding.
//! We use `thread_local!` with a `RefCell` to store the binding frame stack.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use klujur_parser::{KlujurVal, KlujurVar};

/// A unique identifier for a Var, used as a key in binding frames.
/// We use the qualified name as the key since Vars with the same name
/// in the same namespace should share bindings.
type VarId = String;

/// A binding frame containing var bindings for the current dynamic scope.
#[derive(Clone, Default)]
struct BindingFrame {
    /// Map from var qualified name to bound value
    bindings: HashMap<VarId, KlujurVal>,
    /// Previous frame in the stack (for nested bindings)
    prev: Option<Rc<BindingFrame>>,
}

impl BindingFrame {
    /// Create a new frame with bindings, linking to the previous frame.
    fn with_bindings(bindings: HashMap<VarId, KlujurVal>, prev: Option<Rc<BindingFrame>>) -> Self {
        BindingFrame { bindings, prev }
    }

    /// Look up a binding in this frame or its ancestors.
    fn get(&self, var_id: &str) -> Option<KlujurVal> {
        if let Some(val) = self.bindings.get(var_id) {
            Some(val.clone())
        } else if let Some(prev) = &self.prev {
            prev.get(var_id)
        } else {
            None
        }
    }

    /// Check if a var has a thread-local binding in this frame or ancestors.
    fn has_binding(&self, var_id: &str) -> bool {
        self.bindings.contains_key(var_id)
            || self.prev.as_ref().is_some_and(|p| p.has_binding(var_id))
    }
}

thread_local! {
    /// The current binding frame stack.
    /// We use Option<Rc<BindingFrame>> where None means no dynamic bindings are active.
    static CURRENT_FRAME: RefCell<Option<Rc<BindingFrame>>> = const { RefCell::new(None) };
}

/// Push a new binding frame with the given bindings.
/// Returns a guard that will pop the frame when dropped.
pub fn push_bindings(bindings: Vec<(&KlujurVar, KlujurVal)>) -> BindingGuard {
    let mut binding_map = HashMap::new();
    for (var, val) in bindings {
        binding_map.insert(var.qualified_name(), val);
    }

    CURRENT_FRAME.with(|frame_cell| {
        let prev = frame_cell.borrow().clone();
        let new_frame = BindingFrame::with_bindings(binding_map, prev);
        *frame_cell.borrow_mut() = Some(Rc::new(new_frame));
    });

    BindingGuard { _private: () }
}

/// Pop the current binding frame, restoring the previous one.
fn pop_bindings() {
    CURRENT_FRAME.with(|frame_cell| {
        let prev = frame_cell.borrow().as_ref().and_then(|f| f.prev.clone());
        *frame_cell.borrow_mut() = prev;
    });
}

/// RAII guard that pops the binding frame when dropped.
pub struct BindingGuard {
    _private: (),
}

impl Drop for BindingGuard {
    fn drop(&mut self) {
        pop_bindings();
    }
}

/// Get the thread-local binding for a var, if any.
/// Returns None if the var has no thread-local binding.
#[inline]
#[must_use]
pub fn get_thread_binding(var: &KlujurVar) -> Option<KlujurVal> {
    if !var.is_dynamic() {
        return None;
    }

    let var_id = var.qualified_name();
    CURRENT_FRAME.with(|frame_cell| frame_cell.borrow().as_ref().and_then(|f| f.get(&var_id)))
}

/// Check if a var has a thread-local binding.
#[inline]
pub fn has_thread_binding(var: &KlujurVar) -> bool {
    if !var.is_dynamic() {
        return false;
    }

    let var_id = var.qualified_name();
    CURRENT_FRAME.with(|frame_cell| {
        frame_cell
            .borrow()
            .as_ref()
            .is_some_and(|f| f.has_binding(&var_id))
    })
}

/// Set a thread-local binding for a var.
/// Only works if the var already has a thread-local binding (i.e., within a `binding` form).
/// Per Clojure semantics, this updates the nearest binding in the frame stack.
/// Returns true if the binding was updated, false if no binding exists.
pub fn set_thread_binding(var: &KlujurVar, value: KlujurVal) -> bool {
    if !var.is_dynamic() {
        return false;
    }

    let var_id = var.qualified_name();
    CURRENT_FRAME.with(|frame_cell| {
        let mut borrow = frame_cell.borrow_mut();
        if let Some(frame) = borrow.as_mut() {
            // Check if binding exists anywhere in the stack
            if !frame.has_binding(&var_id) {
                return false;
            }

            // Rebuild the frame stack with the updated binding.
            // We need to find the frame containing the binding and update it,
            // while preserving the structure of the stack.
            fn rebuild_with_update(
                frame: &BindingFrame,
                var_id: &str,
                value: KlujurVal,
            ) -> BindingFrame {
                if frame.bindings.contains_key(var_id) {
                    // This frame has the binding - update it
                    let mut new_bindings = frame.bindings.clone();
                    new_bindings.insert(var_id.to_string(), value);
                    BindingFrame {
                        bindings: new_bindings,
                        prev: frame.prev.clone(),
                    }
                } else if let Some(prev) = &frame.prev {
                    // Binding is in an ancestor - recurse
                    let new_prev = rebuild_with_update(prev, var_id, value);
                    BindingFrame {
                        bindings: frame.bindings.clone(),
                        prev: Some(Rc::new(new_prev)),
                    }
                } else {
                    // Shouldn't happen since we checked has_binding above
                    frame.clone()
                }
            }

            let new_frame = rebuild_with_update(frame, &var_id, value);
            *frame = Rc::new(new_frame);
            true
        } else {
            false
        }
    })
}

/// Dereference a var, checking thread-local bindings first.
/// This is the function that should be used instead of KlujurVar::deref()
/// when evaluating code that might have dynamic bindings.
#[inline]
pub fn deref_var(var: &KlujurVar) -> KlujurVal {
    // Check thread-local binding first
    if let Some(val) = get_thread_binding(var) {
        return val;
    }
    // Fall back to root value
    var.deref()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a dynamic var for testing
    fn make_dynamic_var(name: &str, value: KlujurVal) -> KlujurVar {
        let var = KlujurVar::new(name.to_string(), value);
        var.set_dynamic(true);
        var
    }

    /// Create a non-dynamic var for testing
    fn make_static_var(name: &str, value: KlujurVal) -> KlujurVar {
        KlujurVar::new(name.to_string(), value)
    }

    // =========================================================================
    // Basic push/pop mechanics
    // =========================================================================

    #[test]
    fn test_push_bindings_creates_binding() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        // No binding initially
        assert!(!has_thread_binding(&var));
        assert_eq!(get_thread_binding(&var), None);

        // Push a binding
        let _guard = push_bindings(vec![(&var, KlujurVal::int(42))]);

        // Now there's a binding
        assert!(has_thread_binding(&var));
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(42)));
    }

    #[test]
    fn test_binding_guard_pops_on_drop() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        {
            let _guard = push_bindings(vec![(&var, KlujurVal::int(42))]);
            assert!(has_thread_binding(&var));
        }

        // Guard dropped, binding should be gone
        assert!(!has_thread_binding(&var));
    }

    #[test]
    fn test_nested_bindings() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        let _outer = push_bindings(vec![(&var, KlujurVal::int(10))]);
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(10)));

        {
            let _inner = push_bindings(vec![(&var, KlujurVal::int(20))]);
            assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(20)));
        }

        // Inner dropped, should see outer binding again
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(10)));
    }

    #[test]
    fn test_multiple_vars_in_single_frame() {
        let var1 = make_dynamic_var("*a*", KlujurVal::int(1));
        let var2 = make_dynamic_var("*b*", KlujurVal::int(2));

        let _guard = push_bindings(vec![
            (&var1, KlujurVal::int(100)),
            (&var2, KlujurVal::int(200)),
        ]);

        assert_eq!(get_thread_binding(&var1), Some(KlujurVal::int(100)));
        assert_eq!(get_thread_binding(&var2), Some(KlujurVal::int(200)));
    }

    // =========================================================================
    // Non-dynamic vars
    // =========================================================================

    #[test]
    fn test_non_dynamic_var_returns_none() {
        let var = make_static_var("regular-var", KlujurVal::int(1));

        // Even if we try to push a binding
        let _guard = push_bindings(vec![(&var, KlujurVal::int(42))]);

        // Non-dynamic vars always return None
        assert!(!has_thread_binding(&var));
        assert_eq!(get_thread_binding(&var), None);
    }

    #[test]
    fn test_set_thread_binding_fails_for_non_dynamic() {
        let var = make_static_var("regular-var", KlujurVal::int(1));

        // Can't set binding for non-dynamic var
        assert!(!set_thread_binding(&var, KlujurVal::int(42)));
    }

    // =========================================================================
    // set_thread_binding
    // =========================================================================

    #[test]
    fn test_set_thread_binding_updates_value() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        let _guard = push_bindings(vec![(&var, KlujurVal::int(10))]);
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(10)));

        // Update the binding
        assert!(set_thread_binding(&var, KlujurVal::int(99)));
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(99)));
    }

    #[test]
    fn test_set_thread_binding_fails_without_existing_binding() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        // No binding exists, set should fail
        assert!(!set_thread_binding(&var, KlujurVal::int(42)));
    }

    #[test]
    fn test_set_thread_binding_only_affects_current_frame() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        let _outer = push_bindings(vec![(&var, KlujurVal::int(10))]);

        {
            let _inner = push_bindings(vec![(&var, KlujurVal::int(20))]);
            set_thread_binding(&var, KlujurVal::int(25));
            assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(25)));
        }

        // Outer binding should be unchanged
        assert_eq!(get_thread_binding(&var), Some(KlujurVal::int(10)));
    }

    // =========================================================================
    // deref_var
    // =========================================================================

    #[test]
    fn test_deref_var_uses_thread_binding() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        // Root value
        assert_eq!(deref_var(&var), KlujurVal::int(1));

        let _guard = push_bindings(vec![(&var, KlujurVal::int(42))]);

        // Thread binding takes precedence
        assert_eq!(deref_var(&var), KlujurVal::int(42));
    }

    #[test]
    fn test_deref_var_falls_back_to_root() {
        let var = make_dynamic_var("*test*", KlujurVal::int(99));

        // No thread binding, should return root
        assert_eq!(deref_var(&var), KlujurVal::int(99));
    }

    #[test]
    fn test_deref_var_with_nil_binding() {
        let var = make_dynamic_var("*test*", KlujurVal::int(1));

        let _guard = push_bindings(vec![(&var, KlujurVal::Nil)]);

        // Binding to nil should work and return nil
        assert_eq!(deref_var(&var), KlujurVal::Nil);
    }

    // =========================================================================
    // BindingFrame internal tests
    // =========================================================================

    #[test]
    fn test_binding_frame_get_from_ancestor() {
        let mut bindings1 = HashMap::new();
        bindings1.insert("a".to_string(), KlujurVal::int(1));
        let frame1 = Rc::new(BindingFrame::with_bindings(bindings1, None));

        let mut bindings2 = HashMap::new();
        bindings2.insert("b".to_string(), KlujurVal::int(2));
        let frame2 = BindingFrame::with_bindings(bindings2, Some(frame1));

        // Can get from current frame
        assert_eq!(frame2.get("b"), Some(KlujurVal::int(2)));

        // Can get from ancestor frame
        assert_eq!(frame2.get("a"), Some(KlujurVal::int(1)));

        // Missing key returns None
        assert_eq!(frame2.get("c"), None);
    }

    #[test]
    fn test_binding_frame_has_binding_checks_ancestors() {
        let mut bindings1 = HashMap::new();
        bindings1.insert("a".to_string(), KlujurVal::int(1));
        let frame1 = Rc::new(BindingFrame::with_bindings(bindings1, None));

        let bindings2 = HashMap::new();
        let frame2 = BindingFrame::with_bindings(bindings2, Some(frame1));

        // Has binding from ancestor
        assert!(frame2.has_binding("a"));

        // Doesn't have missing binding
        assert!(!frame2.has_binding("b"));
    }
}
