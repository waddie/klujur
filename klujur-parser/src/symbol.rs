// klujur-parser - Symbol type with interning
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Symbols are identifiers that may be optionally namespaced.
//!
//! # Interning
//!
//! Symbols are interned using a global string interner, meaning that two symbols
//! with the same namespace and name will share the same underlying storage. This
//! provides several benefits:
//!
//! - **O(1) equality**: Comparing symbols is a pointer comparison, not string comparison
//! - **O(1) hashing**: Hash is computed from the pointer address
//! - **Memory efficiency**: Identical symbols share storage
//!
//! # Memory Behaviour
//!
//! **Important**: Interned symbols are never deallocated. The global interner
//! maintains strong references (`Arc`) to all symbols created during the program's
//! lifetime. This means:
//!
//! - Memory usage grows monotonically with unique symbols
//! - Symbols created during parsing/evaluation persist until program termination
//! - This is intentional: symbols are typically reused frequently and the memory
//!   overhead is modest for typical programs
//!
//! For long-running applications that dynamically generate many unique symbols
//! (e.g., via `gensym`), be aware that these will accumulate. In practice, most
//! Clojure programs use a bounded set of symbols defined at compile time.
//!
//! # Thread Safety
//!
//! The interner is protected by a `Mutex`, making symbol creation thread-safe.
//! However, this means symbol creation involves lock acquisition. Symbol lookup
//! and comparison are lock-free after creation.

use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex, OnceLock};

/// A symbol with optional namespace.
///
/// Symbols are interned, meaning that two symbols with the same namespace
/// and name will share the same underlying storage.
#[derive(Clone)]
pub struct Symbol {
    inner: Arc<SymbolInner>,
}

#[derive(Debug)]
struct SymbolInner {
    namespace: Option<Arc<str>>,
    name: Arc<str>,
}

/// Global symbol interner
static SYMBOL_INTERNER: OnceLock<Mutex<SymbolInterner>> = OnceLock::new();

/// Key type for the interner: (namespace, name)
type InternerKey = (Option<Arc<str>>, Arc<str>);

struct SymbolInterner {
    /// Map from (namespace, name) to interned symbol
    symbols: HashMap<InternerKey, Arc<SymbolInner>>,
    /// Interned strings for reuse
    strings: HashMap<String, Arc<str>>,
}

impl SymbolInterner {
    fn new() -> Self {
        SymbolInterner {
            symbols: HashMap::new(),
            strings: HashMap::new(),
        }
    }

    fn intern_string(&mut self, s: &str) -> Arc<str> {
        if let Some(interned) = self.strings.get(s) {
            Arc::clone(interned)
        } else {
            let interned: Arc<str> = Arc::from(s);
            self.strings.insert(s.to_string(), Arc::clone(&interned));
            interned
        }
    }

    fn intern(&mut self, namespace: Option<&str>, name: &str) -> Arc<SymbolInner> {
        let ns = namespace.map(|s| self.intern_string(s));
        let n = self.intern_string(name);

        let key = (ns.clone(), n.clone());
        if let Some(existing) = self.symbols.get(&key) {
            Arc::clone(existing)
        } else {
            let inner = Arc::new(SymbolInner {
                namespace: ns.clone(),
                name: n.clone(),
            });
            self.symbols.insert(key, Arc::clone(&inner));
            inner
        }
    }
}

fn get_interner() -> &'static Mutex<SymbolInterner> {
    SYMBOL_INTERNER.get_or_init(|| Mutex::new(SymbolInterner::new()))
}

impl Symbol {
    /// Create a new symbol with no namespace.
    pub fn new(name: &str) -> Self {
        let inner = get_interner()
            .lock()
            .expect(
                "Symbol interner mutex poisoned: another thread panicked while holding the lock",
            )
            .intern(None, name);
        Symbol { inner }
    }

    /// Create a new symbol with a namespace.
    pub fn with_namespace(namespace: &str, name: &str) -> Self {
        let inner = get_interner()
            .lock()
            .expect(
                "Symbol interner mutex poisoned: another thread panicked while holding the lock",
            )
            .intern(Some(namespace), name);
        Symbol { inner }
    }

    /// Parse a symbol from a string like "foo" or "ns/foo".
    pub fn parse(s: &str) -> Self {
        if let Some(slash_pos) = s.find('/') {
            // Handle special case of "/" symbol
            if s == "/" {
                return Symbol::new("/");
            }
            let ns = &s[..slash_pos];
            let name = &s[slash_pos + 1..];
            Symbol::with_namespace(ns, name)
        } else {
            Symbol::new(s)
        }
    }

    /// Get the namespace, if any.
    #[must_use]
    pub fn namespace(&self) -> Option<&str> {
        self.inner.namespace.as_deref()
    }

    /// Get the name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    /// Check if this symbol has a namespace.
    #[must_use]
    pub fn has_namespace(&self) -> bool {
        self.inner.namespace.is_some()
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ns) = &self.inner.namespace {
            write!(f, "{}/{}", ns, self.inner.name)
        } else {
            write!(f, "{}", self.inner.name)
        }
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({})", self)
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        // Due to interning, pointer comparison is sufficient
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Symbol {}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (&self.inner.namespace, &other.inner.namespace) {
            (None, Some(_)) => std::cmp::Ordering::Less,
            (Some(_), None) => std::cmp::Ordering::Greater,
            (None, None) => self.inner.name.cmp(&other.inner.name),
            (Some(a), Some(b)) => match a.cmp(b) {
                std::cmp::Ordering::Equal => self.inner.name.cmp(&other.inner.name),
                other => other,
            },
        }
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Use pointer hash for interned symbols
        Arc::as_ptr(&self.inner).hash(state);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_symbol() {
        let sym = Symbol::new("foo");
        assert_eq!(sym.name(), "foo");
        assert!(sym.namespace().is_none());
        assert_eq!(format!("{}", sym), "foo");
    }

    #[test]
    fn test_namespaced_symbol() {
        let sym = Symbol::with_namespace("user", "foo");
        assert_eq!(sym.name(), "foo");
        assert_eq!(sym.namespace(), Some("user"));
        assert_eq!(format!("{}", sym), "user/foo");
    }

    #[test]
    fn test_parse_simple() {
        let sym = Symbol::parse("foo");
        assert_eq!(sym.name(), "foo");
        assert!(sym.namespace().is_none());
    }

    #[test]
    fn test_parse_namespaced() {
        let sym = Symbol::parse("user/foo");
        assert_eq!(sym.name(), "foo");
        assert_eq!(sym.namespace(), Some("user"));
    }

    #[test]
    fn test_parse_slash_symbol() {
        let sym = Symbol::parse("/");
        assert_eq!(sym.name(), "/");
        assert!(sym.namespace().is_none());
    }

    #[test]
    fn test_interning() {
        let sym1 = Symbol::new("foo");
        let sym2 = Symbol::new("foo");
        assert_eq!(sym1, sym2);
        // Interned symbols share the same Arc
        assert!(Arc::ptr_eq(&sym1.inner, &sym2.inner));
    }

    #[test]
    fn test_equality() {
        let sym1 = Symbol::new("foo");
        let sym2 = Symbol::new("foo");
        let sym3 = Symbol::new("bar");

        assert_eq!(sym1, sym2);
        assert_ne!(sym1, sym3);
    }

    #[test]
    fn test_ordering() {
        let a = Symbol::new("a");
        let b = Symbol::new("b");
        let ns_a = Symbol::with_namespace("ns", "a");

        assert!(a < b);
        assert!(a < ns_a); // Non-namespaced comes before namespaced
    }
}
