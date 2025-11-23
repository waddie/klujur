// klujur-core - Environment for lexical scoping
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Environment for variable bindings with lexical scoping.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use klujur_parser::{KlujurVal, Symbol};

use crate::error::{Error, Result};
use crate::namespace::NamespaceRegistry;

/// A lexical environment for variable bindings.
///
/// Environments form a chain through parent references, enabling
/// lexical scoping. Each environment has its own bindings map
/// and optionally a parent environment for outer scope lookup.
#[derive(Debug, Clone)]
pub struct Env {
    inner: Rc<RefCell<EnvInner>>,
}

#[derive(Debug)]
struct EnvInner {
    bindings: HashMap<Symbol, KlujurVal>,
    parent: Option<Env>,
    /// Namespace registry (only set on root environment)
    registry: Option<NamespaceRegistry>,
}

impl Env {
    /// Create a new root environment with no parent.
    pub fn new() -> Self {
        Env {
            inner: Rc::new(RefCell::new(EnvInner {
                bindings: HashMap::new(),
                parent: None,
                registry: Some(NamespaceRegistry::new()),
            })),
        }
    }

    /// Create a child environment with this environment as parent.
    pub fn child(&self) -> Self {
        Env {
            inner: Rc::new(RefCell::new(EnvInner {
                bindings: HashMap::new(),
                parent: Some(self.clone()),
                registry: None, // Children share parent's registry
            })),
        }
    }

    /// Get the namespace registry from the root environment.
    /// Uses iterative traversal to avoid stack overflow on deep environments.
    pub fn registry(&self) -> NamespaceRegistry {
        let mut current = self.clone();
        loop {
            let inner = current.inner.borrow();
            if let Some(ref registry) = inner.registry {
                return registry.clone();
            }
            let parent = inner.parent.clone();
            drop(inner);
            match parent {
                Some(p) => current = p,
                None => panic!("Root environment missing namespace registry"),
            }
        }
    }

    /// Define a binding in this environment (not parent).
    pub fn define(&self, sym: Symbol, val: KlujurVal) {
        self.inner.borrow_mut().bindings.insert(sym, val);
    }

    /// Look up a symbol in this environment or parent chain.
    /// Uses iterative traversal to avoid stack overflow on deep environments.
    pub fn lookup(&self, sym: &Symbol) -> Result<KlujurVal> {
        let mut current = self.clone();
        loop {
            let inner = current.inner.borrow();
            if let Some(val) = inner.bindings.get(sym) {
                return Ok(val.clone());
            }
            let parent = inner.parent.clone();
            drop(inner);
            match parent {
                Some(p) => current = p,
                None => return Err(Error::UndefinedSymbol(sym.clone())),
            }
        }
    }

    /// Set a binding, looking up the chain to find where it's defined.
    /// Returns an error if the symbol is not defined anywhere.
    /// Uses iterative traversal to avoid stack overflow on deep environments.
    pub fn set(&self, sym: &Symbol, val: KlujurVal) -> Result<()> {
        let mut current = self.clone();
        loop {
            // Check if defined in current environment
            {
                let inner = current.inner.borrow();
                if inner.bindings.contains_key(sym) {
                    drop(inner);
                    current.inner.borrow_mut().bindings.insert(sym.clone(), val);
                    return Ok(());
                }
            }
            // Move to parent
            let parent = current.inner.borrow().parent.clone();
            match parent {
                Some(p) => current = p,
                None => return Err(Error::UndefinedSymbol(sym.clone())),
            }
        }
    }

    /// Check if a symbol is defined in this environment or parent chain.
    /// Uses iterative traversal to avoid stack overflow on deep environments.
    pub fn is_defined(&self, sym: &Symbol) -> bool {
        let mut current = self.clone();
        loop {
            let inner = current.inner.borrow();
            if inner.bindings.contains_key(sym) {
                return true;
            }
            let parent = inner.parent.clone();
            drop(inner);
            match parent {
                Some(p) => current = p,
                None => return false,
            }
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(name: &str) -> Symbol {
        Symbol::new(name)
    }

    #[test]
    fn test_define_and_lookup() {
        let env = Env::new();
        env.define(sym("x"), KlujurVal::int(42));

        assert_eq!(env.lookup(&sym("x")).unwrap(), KlujurVal::int(42));
    }

    #[test]
    fn test_undefined_symbol() {
        let env = Env::new();
        let result = env.lookup(&sym("x"));
        assert!(result.is_err());
    }

    #[test]
    fn test_child_inherits_parent() {
        let parent = Env::new();
        parent.define(sym("x"), KlujurVal::int(42));

        let child = parent.child();
        assert_eq!(child.lookup(&sym("x")).unwrap(), KlujurVal::int(42));
    }

    #[test]
    fn test_child_shadows_parent() {
        let parent = Env::new();
        parent.define(sym("x"), KlujurVal::int(42));

        let child = parent.child();
        child.define(sym("x"), KlujurVal::int(100));

        assert_eq!(child.lookup(&sym("x")).unwrap(), KlujurVal::int(100));
        assert_eq!(parent.lookup(&sym("x")).unwrap(), KlujurVal::int(42));
    }

    #[test]
    fn test_is_defined() {
        let env = Env::new();
        assert!(!env.is_defined(&sym("x")));

        env.define(sym("x"), KlujurVal::int(42));
        assert!(env.is_defined(&sym("x")));
    }

    #[test]
    fn test_set_existing() {
        let env = Env::new();
        env.define(sym("x"), KlujurVal::int(42));
        env.set(&sym("x"), KlujurVal::int(100)).unwrap();

        assert_eq!(env.lookup(&sym("x")).unwrap(), KlujurVal::int(100));
    }

    #[test]
    fn test_set_in_parent() {
        let parent = Env::new();
        parent.define(sym("x"), KlujurVal::int(42));

        let child = parent.child();
        child.set(&sym("x"), KlujurVal::int(100)).unwrap();

        // Parent is updated, not child
        assert_eq!(parent.lookup(&sym("x")).unwrap(), KlujurVal::int(100));
        assert_eq!(child.lookup(&sym("x")).unwrap(), KlujurVal::int(100));
    }
}
