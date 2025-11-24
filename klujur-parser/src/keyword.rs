// klujur-parser - Keyword type with interning
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Keywords are self-evaluating identifiers that may be optionally namespaced.
//!
//! # Interning
//!
//! Keywords are interned using a global string interner, meaning that two keywords
//! with the same namespace and name will share the same underlying storage. This
//! provides several benefits:
//!
//! - **O(1) equality**: Comparing keywords is a pointer comparison, not string comparison
//! - **O(1) hashing**: Hash is computed from the pointer address
//! - **Memory efficiency**: Identical keywords share storage
//!
//! # Memory Behaviour
//!
//! **Important**: Interned keywords are never deallocated. The global interner
//! maintains strong references (`Arc`) to all keywords created during the program's
//! lifetime. This means:
//!
//! - Memory usage grows monotonically with unique keywords
//! - Keywords created during parsing/evaluation persist until program termination
//! - This is intentional: keywords are typically reused frequently and the memory
//!   overhead is modest for typical programs
//!
//! For long-running applications that dynamically generate many unique keywords
//! (e.g., from user input), be aware that these will accumulate. In practice, most
//! Clojure programs use a bounded set of keywords defined at compile time.
//!
//! # Thread Safety
//!
//! The interner is protected by a `Mutex`, making keyword creation thread-safe.
//! However, this means keyword creation involves lock acquisition. Keyword lookup
//! and comparison are lock-free after creation.

use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex, OnceLock};

/// A keyword with optional namespace.
///
/// Keywords are self-evaluating and are interned for efficient comparison.
/// They always start with a colon `:` when printed.
#[derive(Clone)]
pub struct Keyword {
    inner: Arc<KeywordInner>,
}

#[derive(Debug)]
struct KeywordInner {
    namespace: Option<Arc<str>>,
    name: Arc<str>,
}

/// Global keyword interner
static KEYWORD_INTERNER: OnceLock<Mutex<KeywordInterner>> = OnceLock::new();

/// Key type for the interner: (namespace, name)
type InternerKey = (Option<Arc<str>>, Arc<str>);

struct KeywordInterner {
    /// Map from (namespace, name) to interned keyword
    keywords: HashMap<InternerKey, Arc<KeywordInner>>,
    /// Interned strings for reuse
    strings: HashMap<String, Arc<str>>,
}

impl KeywordInterner {
    fn new() -> Self {
        KeywordInterner {
            keywords: HashMap::new(),
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

    fn intern(&mut self, namespace: Option<&str>, name: &str) -> Arc<KeywordInner> {
        let ns = namespace.map(|s| self.intern_string(s));
        let n = self.intern_string(name);

        let key = (ns.clone(), n.clone());
        if let Some(existing) = self.keywords.get(&key) {
            Arc::clone(existing)
        } else {
            let inner = Arc::new(KeywordInner {
                namespace: ns.clone(),
                name: n.clone(),
            });
            self.keywords.insert(key, Arc::clone(&inner));
            inner
        }
    }
}

fn get_interner() -> &'static Mutex<KeywordInterner> {
    KEYWORD_INTERNER.get_or_init(|| Mutex::new(KeywordInterner::new()))
}

impl Keyword {
    /// Create a new keyword with no namespace.
    pub fn new(name: &str) -> Self {
        let inner = get_interner()
            .lock()
            .expect(
                "Keyword interner mutex poisoned: another thread panicked while holding the lock",
            )
            .intern(None, name);
        Keyword { inner }
    }

    /// Create a new keyword with a namespace.
    pub fn with_namespace(namespace: &str, name: &str) -> Self {
        let inner = get_interner()
            .lock()
            .expect(
                "Keyword interner mutex poisoned: another thread panicked while holding the lock",
            )
            .intern(Some(namespace), name);
        Keyword { inner }
    }

    /// Parse a keyword from a string like ":foo" or ":ns/foo".
    /// The leading colon is optional.
    pub fn parse(s: &str) -> Self {
        let s = s.strip_prefix(':').unwrap_or(s);

        if let Some(slash_pos) = s.find('/') {
            let ns = &s[..slash_pos];
            let name = &s[slash_pos + 1..];
            Keyword::with_namespace(ns, name)
        } else {
            Keyword::new(s)
        }
    }

    /// Get the namespace, if any.
    #[inline]
    #[must_use]
    pub fn namespace(&self) -> Option<&str> {
        self.inner.namespace.as_deref()
    }

    /// Get the name.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    /// Check if this keyword has a namespace.
    #[inline]
    #[must_use]
    pub fn has_namespace(&self) -> bool {
        self.inner.namespace.is_some()
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ns) = &self.inner.namespace {
            write!(f, ":{}/{}", ns, self.inner.name)
        } else {
            write!(f, ":{}", self.inner.name)
        }
    }
}

impl fmt::Debug for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Keyword({})", self)
    }
}

impl PartialEq for Keyword {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Due to interning, pointer comparison is sufficient
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Keyword {}

impl PartialOrd for Keyword {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Keyword {
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

impl Hash for Keyword {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Use pointer hash for interned keywords
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
    fn test_simple_keyword() {
        let kw = Keyword::new("foo");
        assert_eq!(kw.name(), "foo");
        assert!(kw.namespace().is_none());
        assert_eq!(format!("{}", kw), ":foo");
    }

    #[test]
    fn test_namespaced_keyword() {
        let kw = Keyword::with_namespace("user", "foo");
        assert_eq!(kw.name(), "foo");
        assert_eq!(kw.namespace(), Some("user"));
        assert_eq!(format!("{}", kw), ":user/foo");
    }

    #[test]
    fn test_parse_simple() {
        let kw = Keyword::parse(":foo");
        assert_eq!(kw.name(), "foo");
        assert!(kw.namespace().is_none());
    }

    #[test]
    fn test_parse_without_colon() {
        let kw = Keyword::parse("foo");
        assert_eq!(kw.name(), "foo");
        assert!(kw.namespace().is_none());
    }

    #[test]
    fn test_parse_namespaced() {
        let kw = Keyword::parse(":user/foo");
        assert_eq!(kw.name(), "foo");
        assert_eq!(kw.namespace(), Some("user"));
    }

    #[test]
    fn test_interning() {
        let kw1 = Keyword::new("foo");
        let kw2 = Keyword::new("foo");
        assert_eq!(kw1, kw2);
        // Interned keywords share the same Arc
        assert!(Arc::ptr_eq(&kw1.inner, &kw2.inner));
    }

    #[test]
    fn test_equality() {
        let kw1 = Keyword::new("foo");
        let kw2 = Keyword::new("foo");
        let kw3 = Keyword::new("bar");

        assert_eq!(kw1, kw2);
        assert_ne!(kw1, kw3);
    }

    #[test]
    fn test_ordering() {
        let a = Keyword::new("a");
        let b = Keyword::new("b");
        let ns_a = Keyword::with_namespace("ns", "a");

        assert!(a < b);
        assert!(a < ns_a); // Non-namespaced comes before namespaced
    }
}
