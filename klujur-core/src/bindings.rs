// klujur-core - Dynamic binding frame management
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Thread-local binding frames for dynamic vars.
//!
//! This module provides the infrastructure for Clojure-style dynamic binding.
//! Since Klujur uses `Rc` (single-threaded), we use a global `RefCell` instead
//! of true thread-local storage.

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

    /// Set a binding in the current frame (for set! within binding context).
    /// Returns true if the binding was found and updated.
    fn set(&mut self, var_id: &str, value: KlujurVal) -> bool {
        if self.bindings.contains_key(var_id) {
            self.bindings.insert(var_id.to_string(), value);
            true
        } else {
            false
        }
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
pub fn get_thread_binding(var: &KlujurVar) -> Option<KlujurVal> {
    if !var.is_dynamic() {
        return None;
    }

    let var_id = var.qualified_name();
    CURRENT_FRAME.with(|frame_cell| frame_cell.borrow().as_ref().and_then(|f| f.get(&var_id)))
}

/// Check if a var has a thread-local binding.
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
/// Returns true if the binding was updated, false if no binding exists.
pub fn set_thread_binding(var: &KlujurVar, value: KlujurVal) -> bool {
    if !var.is_dynamic() {
        return false;
    }

    let var_id = var.qualified_name();
    CURRENT_FRAME.with(|frame_cell| {
        let mut borrow = frame_cell.borrow_mut();
        if let Some(frame) = borrow.as_mut() {
            // We need to mutate the frame, so we need to get a mutable reference
            // Since we're using Rc, we need to clone and replace
            let mut new_frame = (**frame).clone();
            if new_frame.set(&var_id, value) {
                *frame = Rc::new(new_frame);
                return true;
            }
        }
        false
    })
}

/// Dereference a var, checking thread-local bindings first.
/// This is the function that should be used instead of KlujurVar::deref()
/// when evaluating code that might have dynamic bindings.
pub fn deref_var(var: &KlujurVar) -> KlujurVal {
    // Check thread-local binding first
    if let Some(val) = get_thread_binding(var) {
        return val;
    }
    // Fall back to root value
    var.deref()
}
