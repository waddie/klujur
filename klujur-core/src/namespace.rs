// klujur-core - Namespace system for global bindings
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Namespace system for managing global variable bindings.
//!
//! Namespaces provide a way to organise and isolate Vars. Each namespace
//! contains a mapping from symbols to Vars. The `def` special form creates
//! Vars in the current namespace.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::rc::Rc;

use klujur_parser::{KlujurHierarchy, KlujurVal, KlujurVar, Protocol, RecordDef, Symbol};

/// A namespace containing Var bindings.
///
/// Namespaces are the primary mechanism for organising global bindings.
/// Each namespace has a name and a mapping from symbols to Vars.
#[derive(Debug, Clone)]
pub struct Namespace {
    inner: Rc<RefCell<NamespaceInner>>,
}

#[derive(Debug)]
struct NamespaceInner {
    /// The namespace name (e.g., "user", "clojure.core")
    /// Uses Rc<str> to avoid cloning on every name() call
    name: Rc<str>,
    /// Mapping from symbol names to Vars
    vars: HashMap<String, KlujurVar>,
    /// Aliases to other namespaces (for require :as)
    aliases: HashMap<String, Namespace>,
    /// Refers from other namespaces (for use/refer)
    refers: HashMap<String, KlujurVar>,
}

impl Namespace {
    /// Create a new namespace with the given name.
    pub fn new(name: impl Into<String>) -> Self {
        Namespace {
            inner: Rc::new(RefCell::new(NamespaceInner {
                name: Rc::from(name.into()),
                vars: HashMap::new(),
                aliases: HashMap::new(),
                refers: HashMap::new(),
            })),
        }
    }

    /// Get the namespace name.
    /// Returns a clone of the Rc<str>, which is cheap (just increments refcount).
    #[inline]
    #[must_use]
    pub fn name(&self) -> String {
        self.inner.borrow().name.to_string()
    }

    /// Get the namespace name as an Rc<str> for cheap sharing.
    #[inline]
    #[must_use]
    pub fn name_rc(&self) -> Rc<str> {
        self.inner.borrow().name.clone()
    }

    /// Intern a Var with the given name, creating it if it doesn't exist.
    /// Returns the existing Var if one already exists.
    pub fn intern(&self, name: impl Into<String>) -> KlujurVar {
        let name = name.into();
        let mut inner = self.inner.borrow_mut();

        if let Some(var) = inner.vars.get(&name) {
            return var.clone();
        }

        let ns_name = inner.name.to_string();
        let var = KlujurVar::new_with_ns(ns_name, name.clone(), KlujurVal::Nil);
        inner.vars.insert(name, var.clone());
        var
    }

    /// Intern a Var with the given name and value.
    /// Updates the root value if the Var already exists.
    pub fn intern_with_value(&self, name: impl Into<String>, value: KlujurVal) -> KlujurVar {
        let var = self.intern(name);
        var.set_root(value);
        var
    }

    /// Intern a dynamic Var with the given name and value.
    /// Dynamic vars can be rebound using the `binding` special form.
    pub fn intern_dynamic(&self, name: impl Into<String>, value: KlujurVal) -> KlujurVar {
        let var = self.intern_with_value(name, value);
        var.set_dynamic(true);
        var
    }

    /// Look up a Var by name in this namespace.
    /// Does not check refers or aliases.
    #[inline]
    #[must_use]
    pub fn find_var(&self, name: &str) -> Option<KlujurVar> {
        self.inner.borrow().vars.get(name).cloned()
    }

    /// Resolve a symbol to a Var, checking local vars, then refers.
    #[inline]
    #[must_use]
    pub fn resolve(&self, sym: &Symbol) -> Option<KlujurVar> {
        let inner = self.inner.borrow();

        // Check for qualified symbol (ns/name)
        if let Some(ns_name) = sym.namespace() {
            // Look up in aliases first
            if let Some(alias_ns) = inner.aliases.get(ns_name) {
                return alias_ns.find_var(sym.name());
            }
            // Otherwise, we'd need to look up the namespace by name
            // For now, return None if not found in aliases
            return None;
        }

        // Unqualified symbol - check local vars first
        if let Some(var) = inner.vars.get(sym.name()) {
            return Some(var.clone());
        }

        // Then check refers
        if let Some(var) = inner.refers.get(sym.name()) {
            return Some(var.clone());
        }

        None
    }

    /// Add an alias for another namespace.
    pub fn add_alias(&self, alias: impl Into<String>, ns: Namespace) {
        self.inner.borrow_mut().aliases.insert(alias.into(), ns);
    }

    /// Add a refer from another namespace's Var.
    pub fn refer(&self, name: impl Into<String>, var: KlujurVar) {
        self.inner.borrow_mut().refers.insert(name.into(), var);
    }

    /// Get all Vars in this namespace (same as interns).
    #[must_use]
    pub fn vars(&self) -> HashMap<String, KlujurVar> {
        self.inner.borrow().vars.clone()
    }

    /// Get all interned Vars in this namespace.
    /// This includes both public and private vars.
    #[must_use]
    pub fn interns(&self) -> HashMap<String, KlujurVar> {
        self.inner.borrow().vars.clone()
    }

    /// Get only public Vars in this namespace.
    /// Filters out vars marked with ^:private metadata.
    pub fn publics(&self) -> HashMap<String, KlujurVar> {
        self.inner
            .borrow()
            .vars
            .iter()
            .filter(|(_, var)| var.is_public())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
}

impl PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name()
    }
}

/// Global registry of all namespaces.
///
/// This maintains a mapping from namespace names to Namespace instances.
/// Use `find_or_create` to get a namespace by name.
#[derive(Debug, Clone)]
pub struct NamespaceRegistry {
    inner: Rc<RefCell<RegistryInner>>,
}

#[derive(Debug)]
struct RegistryInner {
    namespaces: HashMap<String, Namespace>,
    /// Current namespace name. Uses Rc<str> to avoid cloning on current_name() calls.
    current: Rc<str>,
    /// Track which namespaces have been loaded from files
    loaded: HashSet<String>,
    /// Paths to search for namespace files
    load_paths: Vec<PathBuf>,
    /// Global hierarchy for derive/isa? relationships
    global_hierarchy: Rc<RefCell<KlujurHierarchy>>,
    /// Registered protocols (qualified name -> Protocol)
    protocols: HashMap<String, Rc<Protocol>>,
    /// Registered record types (qualified name -> RecordDef)
    records: HashMap<String, RecordDef>,
    /// Embedded namespace sources (for stdlib namespaces loaded on require)
    embedded_sources: HashMap<String, &'static str>,
}

impl NamespaceRegistry {
    /// The name of the core namespace (analogous to clojure.core).
    pub const CORE_NS: &'static str = "klujur.core";

    /// Create a new registry with "klujur.core" and "user" namespaces.
    /// The "user" namespace is set as current.
    pub fn new() -> Self {
        let mut namespaces = HashMap::new();
        let klujur_core = Namespace::new(Self::CORE_NS);
        let user_ns = Namespace::new("user");
        namespaces.insert(Self::CORE_NS.to_string(), klujur_core);
        namespaces.insert("user".to_string(), user_ns);

        NamespaceRegistry {
            inner: Rc::new(RefCell::new(RegistryInner {
                namespaces,
                current: Rc::from("user"),
                loaded: HashSet::new(),
                load_paths: vec![PathBuf::from("src"), PathBuf::from("lib")],
                global_hierarchy: Rc::new(RefCell::new(KlujurHierarchy::new())),
                protocols: HashMap::new(),
                records: HashMap::new(),
                embedded_sources: HashMap::new(),
            })),
        }
    }

    /// Get the global hierarchy for derive/isa? relationships.
    #[inline]
    pub fn global_hierarchy(&self) -> Rc<RefCell<KlujurHierarchy>> {
        self.inner.borrow().global_hierarchy.clone()
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Protocol Registry
    // ─────────────────────────────────────────────────────────────────────────

    /// Register a protocol with a qualified name (ns/name).
    pub fn register_protocol(&self, protocol: Protocol) -> Rc<Protocol> {
        let qualified_name = format!("{}/{}", protocol.ns, protocol.name);
        let proto_rc = Rc::new(protocol);
        self.inner
            .borrow_mut()
            .protocols
            .insert(qualified_name, proto_rc.clone());
        proto_rc
    }

    /// Find a protocol by its qualified name (ns/name).
    pub fn find_protocol(&self, qualified_name: &str) -> Option<Rc<Protocol>> {
        self.inner.borrow().protocols.get(qualified_name).cloned()
    }

    /// Find a protocol by namespace and name.
    pub fn find_protocol_by_parts(&self, ns: &str, name: &str) -> Option<Rc<Protocol>> {
        let qualified_name = format!("{}/{}", ns, name);
        self.find_protocol(&qualified_name)
    }

    /// Find a protocol by simple name, searching in the current namespace first.
    /// If not found, searches all namespaces.
    pub fn resolve_protocol(&self, name: &str) -> Option<Rc<Protocol>> {
        let inner = self.inner.borrow();

        // Try current namespace first
        let qualified = format!("{}/{}", inner.current, name);
        if let Some(proto) = inner.protocols.get(&qualified) {
            return Some(proto.clone());
        }

        // Search all protocols for a match by simple name
        for (key, proto) in &inner.protocols {
            if key.ends_with(&format!("/{}", name)) {
                return Some(proto.clone());
            }
        }

        None
    }

    /// Get all registered protocols.
    pub fn all_protocols(&self) -> HashMap<String, Rc<Protocol>> {
        self.inner.borrow().protocols.clone()
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Record Registry
    // ─────────────────────────────────────────────────────────────────────────

    /// Register a record type with a qualified name (ns/name).
    pub fn register_record(&self, record_def: RecordDef) {
        let qualified_name = record_def.qualified_name();
        self.inner
            .borrow_mut()
            .records
            .insert(qualified_name, record_def);
    }

    /// Find a record definition by its qualified name (ns/name).
    pub fn find_record(&self, qualified_name: &str) -> Option<RecordDef> {
        self.inner.borrow().records.get(qualified_name).cloned()
    }

    /// Find a record definition by namespace and name.
    pub fn find_record_by_parts(&self, ns: &str, name: &str) -> Option<RecordDef> {
        let qualified_name = format!("{}/{}", ns, name);
        self.find_record(&qualified_name)
    }

    /// Find a record by simple name, searching in the current namespace first.
    /// If not found, searches all namespaces.
    pub fn resolve_record(&self, name: &str) -> Option<RecordDef> {
        let inner = self.inner.borrow();

        // Try current namespace first
        let qualified = format!("{}/{}", inner.current, name);
        if let Some(rec) = inner.records.get(&qualified) {
            return Some(rec.clone());
        }

        // Search all records for a match by simple name
        for (key, rec) in &inner.records {
            if key.ends_with(&format!("/{}", name)) {
                return Some(rec.clone());
            }
        }

        None
    }

    /// Get all registered record types.
    pub fn all_records(&self) -> HashMap<String, RecordDef> {
        self.inner.borrow().records.clone()
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Dependency Tracking
    // ─────────────────────────────────────────────────────────────────────────

    /// Check if a namespace has been loaded from a file.
    #[must_use]
    pub fn is_loaded(&self, ns_name: &str) -> bool {
        self.inner.borrow().loaded.contains(ns_name)
    }

    /// Mark a namespace as loaded.
    pub fn mark_loaded(&self, ns_name: impl Into<String>) {
        self.inner.borrow_mut().loaded.insert(ns_name.into());
    }

    /// Remove a namespace from the loaded set (for reloading).
    pub fn reload(&self, ns_name: &str) {
        self.inner.borrow_mut().loaded.remove(ns_name);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Load Path Management
    // ─────────────────────────────────────────────────────────────────────────

    /// Get the current load paths.
    pub fn load_paths(&self) -> Vec<PathBuf> {
        self.inner.borrow().load_paths.clone()
    }

    /// Add a path to the load path list.
    pub fn add_load_path(&self, path: impl Into<PathBuf>) {
        self.inner.borrow_mut().load_paths.push(path.into());
    }

    /// Set the load paths (replaces existing).
    pub fn set_load_paths(&self, paths: Vec<PathBuf>) {
        self.inner.borrow_mut().load_paths = paths;
    }

    /// Find the file path for a namespace.
    /// Converts namespace symbol to path (e.g., "mylib.utils" -> "mylib/utils.klj")
    /// and searches each load path.
    pub fn find_namespace_file(&self, ns_name: &str) -> Option<PathBuf> {
        let relative = ns_name.replace('.', "/") + ".klj";

        for load_path in &self.inner.borrow().load_paths {
            let full_path = load_path.join(&relative);
            if full_path.exists() {
                return Some(full_path);
            }
        }
        None
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Embedded Sources (for stdlib namespaces)
    // ─────────────────────────────────────────────────────────────────────────

    /// Register an embedded source for a namespace.
    /// This allows namespaces to be loaded via `require` without file system access.
    /// Used for stdlib namespaces like `klujur.test`.
    pub fn register_embedded_source(&self, ns_name: &str, source: &'static str) {
        self.inner
            .borrow_mut()
            .embedded_sources
            .insert(ns_name.to_string(), source);
    }

    /// Get the embedded source for a namespace, if registered.
    pub fn get_embedded_source(&self, ns_name: &str) -> Option<&'static str> {
        self.inner.borrow().embedded_sources.get(ns_name).copied()
    }

    /// Find a namespace by name, or create it if it doesn't exist.
    /// New namespaces (except klujur.core) automatically refer all klujur.core publics.
    pub fn find_or_create(&self, name: impl Into<String>) -> Namespace {
        let name = name.into();
        let mut inner = self.inner.borrow_mut();

        if let Some(ns) = inner.namespaces.get(&name) {
            return ns.clone();
        }

        let ns = Namespace::new(name.clone());

        // Auto-refer klujur.core for all namespaces except klujur.core itself
        if name != Self::CORE_NS
            && let Some(core_ns) = inner.namespaces.get(Self::CORE_NS)
        {
            for (var_name, var) in core_ns.publics() {
                ns.refer(var_name, var);
            }
        }

        inner.namespaces.insert(name, ns.clone());
        ns
    }

    /// Refer all public vars from klujur.core into the given namespace.
    /// Called during initialization to set up the user namespace.
    pub fn refer_core_to(&self, ns: &Namespace) {
        let inner = self.inner.borrow();
        if let Some(core_ns) = inner.namespaces.get(Self::CORE_NS) {
            for (var_name, var) in core_ns.publics() {
                ns.refer(var_name, var);
            }
        }
    }

    /// Find a namespace by name, returning None if it doesn't exist.
    pub fn find(&self, name: &str) -> Option<Namespace> {
        self.inner.borrow().namespaces.get(name).cloned()
    }

    /// Get the current namespace.
    pub fn current(&self) -> Namespace {
        let inner = self.inner.borrow();
        inner
            .namespaces
            .get(&*inner.current)
            .cloned()
            .expect("Current namespace should always exist")
    }

    /// Get the current namespace name.
    pub fn current_name(&self) -> String {
        self.inner.borrow().current.to_string()
    }

    /// Get the current namespace name as Rc<str> for cheap sharing.
    pub fn current_name_rc(&self) -> Rc<str> {
        self.inner.borrow().current.clone()
    }

    /// Set the current namespace by name, creating it if necessary.
    pub fn set_current(&self, name: impl Into<String>) -> Namespace {
        let name = name.into();
        let ns = self.find_or_create(name.clone());
        self.inner.borrow_mut().current = Rc::from(name);
        ns
    }

    /// Resolve a symbol to a Var using the current namespace.
    pub fn resolve(&self, sym: &Symbol) -> Option<KlujurVar> {
        let inner = self.inner.borrow();

        // Handle qualified symbols
        if let Some(ns_name) = sym.namespace() {
            // Look up the namespace by name
            if let Some(ns) = inner.namespaces.get(ns_name) {
                return ns.find_var(sym.name());
            }
            // Also check aliases in current namespace
            let current_ns = inner.namespaces.get(&*inner.current)?;
            return current_ns.resolve(sym);
        }

        // Unqualified - use current namespace
        let current_ns = inner.namespaces.get(&*inner.current)?;
        current_ns.resolve(sym)
    }

    /// List all namespace names.
    pub fn all_ns(&self) -> Vec<String> {
        self.inner.borrow().namespaces.keys().cloned().collect()
    }

    /// Remove a namespace from the registry.
    /// Returns true if the namespace existed and was removed.
    /// Cannot remove the current namespace.
    pub fn remove_ns(&self, name: &str) -> bool {
        let mut inner = self.inner.borrow_mut();
        if &*inner.current == name {
            return false;
        }
        inner.loaded.remove(name);
        inner.namespaces.remove(name).is_some()
    }
}

impl Default for NamespaceRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_namespace_creation() {
        let ns = Namespace::new("test.core");
        assert_eq!(ns.name(), "test.core");
    }

    #[test]
    fn test_intern_var() {
        let ns = Namespace::new("test");
        let var1 = ns.intern("foo");
        let var2 = ns.intern("foo");

        // Should return the same Var
        assert_eq!(var1, var2);
        assert_eq!(var1.qualified_name(), "test/foo");
    }

    #[test]
    fn test_intern_with_value() {
        let ns = Namespace::new("test");
        let var = ns.intern_with_value("x", KlujurVal::int(42));

        assert_eq!(var.deref(), KlujurVal::int(42));

        // Interning again with different value updates the var
        let var2 = ns.intern_with_value("x", KlujurVal::int(100));
        assert_eq!(var.deref(), KlujurVal::int(100));
        assert_eq!(var2.deref(), KlujurVal::int(100));
    }

    #[test]
    fn test_find_var() {
        let ns = Namespace::new("test");
        ns.intern_with_value("x", KlujurVal::int(42));

        let found = ns.find_var("x");
        assert!(found.is_some());
        assert_eq!(found.unwrap().deref(), KlujurVal::int(42));

        let not_found = ns.find_var("y");
        assert!(not_found.is_none());
    }

    #[test]
    fn test_resolve_unqualified() {
        let ns = Namespace::new("test");
        ns.intern_with_value("x", KlujurVal::int(42));

        let sym = Symbol::new("x");
        let resolved = ns.resolve(&sym);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap().deref(), KlujurVal::int(42));
    }

    #[test]
    fn test_registry_current() {
        let registry = NamespaceRegistry::new();
        assert_eq!(registry.current_name(), "user");

        let user_ns = registry.current();
        assert_eq!(user_ns.name(), "user");
    }

    #[test]
    fn test_registry_set_current() {
        let registry = NamespaceRegistry::new();
        registry.set_current("test.core");

        assert_eq!(registry.current_name(), "test.core");
        assert_eq!(registry.current().name(), "test.core");
    }

    #[test]
    fn test_registry_resolve() {
        let registry = NamespaceRegistry::new();
        let user_ns = registry.current();
        user_ns.intern_with_value("x", KlujurVal::int(42));

        let sym = Symbol::new("x");
        let resolved = registry.resolve(&sym);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap().deref(), KlujurVal::int(42));
    }

    #[test]
    fn test_registry_resolve_qualified() {
        let registry = NamespaceRegistry::new();

        // Create and populate a different namespace
        let other_ns = registry.find_or_create("other");
        other_ns.intern_with_value("y", KlujurVal::int(100));

        // Resolve qualified symbol from user namespace
        let sym = Symbol::with_namespace("other", "y");
        let resolved = registry.resolve(&sym);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap().deref(), KlujurVal::int(100));
    }

    #[test]
    fn test_namespace_alias() {
        let ns = Namespace::new("test");
        let other_ns = Namespace::new("some.long.name");
        other_ns.intern_with_value("x", KlujurVal::int(42));

        ns.add_alias("short", other_ns);

        let sym = Symbol::with_namespace("short", "x");
        let resolved = ns.resolve(&sym);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap().deref(), KlujurVal::int(42));
    }

    #[test]
    fn test_namespace_refer() {
        let ns = Namespace::new("test");
        let other_ns = Namespace::new("other");
        let var = other_ns.intern_with_value("x", KlujurVal::int(42));

        ns.refer("x", var);

        let sym = Symbol::new("x");
        let resolved = ns.resolve(&sym);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap().deref(), KlujurVal::int(42));
    }

    #[test]
    fn test_publics_excludes_private() {
        use klujur_parser::{Keyword, OrdMap};

        let ns = Namespace::new("test");

        // Create a public var
        let _public_var = ns.intern_with_value("public-fn", KlujurVal::int(1));

        // Create a private var with metadata
        let private_var = ns.intern_with_value("private-fn", KlujurVal::int(2));
        let mut meta = OrdMap::new();
        meta.insert(
            KlujurVal::Keyword(Keyword::new("private")),
            KlujurVal::bool(true),
        );
        private_var.set_meta(Some(meta));

        // publics() should only include public vars
        let publics = ns.publics();
        assert!(publics.contains_key("public-fn"));
        assert!(!publics.contains_key("private-fn"));

        // interns() should include both
        let interns = ns.interns();
        assert!(interns.contains_key("public-fn"));
        assert!(interns.contains_key("private-fn"));
    }

    #[test]
    fn test_var_is_public() {
        use klujur_parser::{Keyword, OrdMap};

        // Var without metadata is public
        let var1 = KlujurVar::new("x".to_string(), KlujurVal::int(1));
        assert!(var1.is_public());

        // Var with empty metadata is public
        let var2 = KlujurVar::new("y".to_string(), KlujurVal::int(2));
        var2.set_meta(Some(OrdMap::new()));
        assert!(var2.is_public());

        // Var with :private false is public
        let var3 = KlujurVar::new("z".to_string(), KlujurVal::int(3));
        let mut meta3 = OrdMap::new();
        meta3.insert(
            KlujurVal::Keyword(Keyword::new("private")),
            KlujurVal::bool(false),
        );
        var3.set_meta(Some(meta3));
        assert!(var3.is_public());

        // Var with :private true is NOT public
        let var4 = KlujurVar::new("w".to_string(), KlujurVal::int(4));
        let mut meta4 = OrdMap::new();
        meta4.insert(
            KlujurVal::Keyword(Keyword::new("private")),
            KlujurVal::bool(true),
        );
        var4.set_meta(Some(meta4));
        assert!(!var4.is_public());
    }
}
