// klujur-parser - Value types for Klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Core value type for Klujur.
//!
//! `KlujurVal` is the central enum representing all Klujur values.

// Allow mutable key types - KlujurVal has interior mutability for Vars/Atoms by design
#![allow(clippy::mutable_key_type)]

use std::any::Any;
use std::cell::Cell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use im::{OrdMap, OrdSet, Vector};

use crate::hierarchy::KlujurHierarchy;

// Thread-local print settings (can be configured by runtime)
thread_local! {
    /// Maximum number of elements to print in a sequence.
    /// None means unlimited, Some(n) means print at most n elements.
    /// Default: None (unlimited)
    static PRINT_LENGTH: Cell<Option<usize>> = const { Cell::new(None) };
}

/// Get the current print-length setting.
#[must_use]
pub fn get_print_length() -> Option<usize> {
    PRINT_LENGTH.with(|pl| pl.get())
}

/// Set the print-length setting. Returns the previous value.
pub fn set_print_length(len: Option<usize>) -> Option<usize> {
    PRINT_LENGTH.with(|pl| pl.replace(len))
}

use crate::keyword::Keyword;
use crate::symbol::Symbol;

// ============================================================================
// CustomType - for Embedding Arbitrary Rust Types
// ============================================================================

/// Trait for embedding custom Rust types as Klujur values.
///
/// Implement this trait to allow arbitrary Rust types to be used as Klujur values.
/// Custom types are opaque to Klujur code but can be passed to and returned from
/// native functions.
///
/// # Example
///
/// ```rust,ignore
/// use klujur_parser::{CustomType, KlujurVal};
///
/// struct MyData {
///     value: i32,
/// }
///
/// impl CustomType for MyData {
///     fn type_name(&self) -> &'static str {
///         "MyData"
///     }
///
///     fn as_any(&self) -> &dyn std::any::Any {
///         self
///     }
/// }
///
/// // Use with KlujurVal::custom()
/// let val = KlujurVal::custom(MyData { value: 42 });
/// ```
pub trait CustomType: fmt::Debug {
    /// Returns the type name for display and error messages.
    fn type_name(&self) -> &'static str;

    /// Returns a reference to the underlying value as `Any` for downcasting.
    fn as_any(&self) -> &dyn Any;

    /// Returns a mutable reference to the underlying value as `Any` for downcasting.
    /// Default implementation returns `None` (immutable).
    fn as_any_mut(&mut self) -> Option<&mut dyn Any> {
        None
    }

    /// Compare two custom values for equality.
    /// Default implementation uses pointer equality.
    fn eq(&self, _other: &dyn CustomType) -> bool {
        false // By default, custom types are only equal to themselves
    }

    /// Return a hash value for this custom type.
    /// Default implementation returns 0 (all values of the same type hash identically).
    fn custom_hash(&self) -> u64 {
        0
    }

    /// Display the custom value.
    /// Default implementation shows `#<TypeName>`.
    fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<{}>", self.type_name())
    }
}

/// Wrapper for custom types that implements necessary traits.
#[derive(Clone)]
pub struct KlujurCustom {
    inner: Rc<dyn CustomType>,
}

impl KlujurCustom {
    /// Create a new custom value wrapper.
    pub fn new<T: CustomType + 'static>(value: T) -> Self {
        KlujurCustom {
            inner: Rc::new(value),
        }
    }

    /// Get the type name of the wrapped value.
    #[must_use]
    pub fn type_name(&self) -> &'static str {
        self.inner.type_name()
    }

    /// Attempt to downcast to a specific type.
    #[must_use]
    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        self.inner.as_any().downcast_ref::<T>()
    }
}

impl fmt::Debug for KlujurCustom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "KlujurCustom({:?})", &*self.inner)
    }
}

impl fmt::Display for KlujurCustom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.display(f)
    }
}

impl PartialEq for KlujurCustom {
    fn eq(&self, other: &Self) -> bool {
        // First check if they're the same Rc
        Rc::ptr_eq(&self.inner, &other.inner) || self.inner.eq(&*other.inner)
    }
}

impl Eq for KlujurCustom {}

impl PartialOrd for KlujurCustom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurCustom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by type name, then by pointer address
        match self.type_name().cmp(other.type_name()) {
            std::cmp::Ordering::Equal => {
                let self_ptr = Rc::as_ptr(&self.inner) as *const () as usize;
                let other_ptr = Rc::as_ptr(&other.inner) as *const () as usize;
                self_ptr.cmp(&other_ptr)
            }
            ord => ord,
        }
    }
}

impl Hash for KlujurCustom {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.type_name().hash(state);
        self.inner.custom_hash().hash(state);
    }
}

// ============================================================================
// TypeKey - for Protocol Dispatch
// ============================================================================

/// Type key for protocol dispatch.
///
/// Used to look up protocol implementations for a given value's type.
/// This is more coarse-grained than the full KlujurVal enum - it groups
/// all function types together, etc.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum TypeKey {
    Nil,
    Bool,
    Int,
    Float,
    Ratio,
    Char,
    String,
    Symbol,
    Keyword,
    List,
    Vector,
    Map,
    Set,
    Fn,
    Var,
    Atom,
    Delay,
    LazySeq,
    Multimethod,
    Hierarchy,
    Reduced,
    Volatile,
    /// Sorted map with custom comparator
    SortedMapBy,
    /// Sorted set with custom comparator
    SortedSetBy,
    /// Custom record types (for future defrecord support)
    Record(crate::symbol::Symbol),
    /// Custom embedded Rust type
    Custom(&'static str),
}

// ============================================================================
// Protocol Types
// ============================================================================

/// A method signature in a protocol.
#[derive(Clone, Debug)]
pub struct MethodSignature {
    /// Method name
    pub name: crate::symbol::Symbol,
    /// Argument lists (multiple arities possible)
    /// Each inner Vec contains parameter symbols including 'this'
    pub arglists: Vec<Vec<crate::symbol::Symbol>>,
    /// Optional docstring
    pub doc: Option<String>,
}

/// Implementation of protocol methods for a specific type.
#[derive(Clone, Debug)]
pub struct TypeImpl {
    /// Method implementations: method name -> function value
    pub methods: std::collections::HashMap<String, KlujurVal>,
}

impl TypeImpl {
    /// Create a new empty TypeImpl
    pub fn new() -> Self {
        TypeImpl {
            methods: std::collections::HashMap::new(),
        }
    }
}

impl Default for TypeImpl {
    fn default() -> Self {
        Self::new()
    }
}

/// A protocol defining a set of methods that can be extended to types.
///
/// Protocols provide polymorphism based on the type of the first argument.
#[derive(Clone)]
pub struct Protocol {
    /// Protocol name
    pub name: crate::symbol::Symbol,
    /// Namespace where the protocol was defined
    pub ns: String,
    /// Method signatures: method name -> signature
    pub methods: std::collections::HashMap<String, MethodSignature>,
    /// Type implementations: type key -> method implementations
    pub impls: Rc<RefCell<std::collections::HashMap<TypeKey, TypeImpl>>>,
}

impl Protocol {
    /// Create a new protocol
    pub fn new(name: crate::symbol::Symbol, ns: String) -> Self {
        Protocol {
            name,
            ns,
            methods: std::collections::HashMap::new(),
            impls: Rc::new(RefCell::new(std::collections::HashMap::new())),
        }
    }

    /// Add a method signature to the protocol
    pub fn add_method(&mut self, sig: MethodSignature) {
        self.methods.insert(sig.name.name().to_string(), sig);
    }

    /// Get the implementation for a type
    #[must_use]
    pub fn get_impl(&self, type_key: &TypeKey) -> Option<TypeImpl> {
        self.impls.borrow().get(type_key).cloned()
    }

    /// Check if a type has an implementation for this protocol
    pub fn has_impl(&self, type_key: &TypeKey) -> bool {
        self.impls.borrow().contains_key(type_key)
    }

    /// Add or update implementation for a type
    pub fn extend_type(&self, type_key: TypeKey, type_impl: TypeImpl) {
        self.impls.borrow_mut().insert(type_key, type_impl);
    }

    /// Add a method implementation to an existing type implementation
    pub fn add_method_impl(&self, type_key: TypeKey, method_name: String, method_fn: KlujurVal) {
        let mut impls = self.impls.borrow_mut();
        impls
            .entry(type_key)
            .or_default()
            .methods
            .insert(method_name, method_fn);
    }
}

impl fmt::Debug for Protocol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Protocol {}/{}>", self.ns, self.name)
    }
}

impl fmt::Display for Protocol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.ns, self.name)
    }
}

impl PartialEq for Protocol {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.ns == other.ns
    }
}

impl Eq for Protocol {}

impl PartialOrd for Protocol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Protocol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.ns.cmp(&other.ns) {
            std::cmp::Ordering::Equal => self.name.cmp(&other.name),
            other => other,
        }
    }
}

impl Hash for Protocol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.ns.hash(state);
    }
}

/// Wrapper for protocol in KlujurVal
#[derive(Clone)]
pub struct KlujurProtocol(pub Rc<Protocol>);

impl KlujurProtocol {
    pub fn new(protocol: Protocol) -> Self {
        KlujurProtocol(Rc::new(protocol))
    }

    pub fn protocol(&self) -> &Protocol {
        &self.0
    }
}

impl fmt::Debug for KlujurProtocol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for KlujurProtocol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq for KlujurProtocol {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

impl Eq for KlujurProtocol {}

impl PartialOrd for KlujurProtocol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurProtocol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl Hash for KlujurProtocol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

// ============================================================================
// Record Types
// ============================================================================

/// Definition of a record type (created by defrecord).
///
/// This stores the schema for a record type: its name, namespace, and field names.
/// Record definitions are registered in the namespace registry.
#[derive(Clone, Debug)]
pub struct RecordDef {
    /// Record type name (e.g., `Person`)
    pub name: Symbol,
    /// Namespace where the record was defined
    pub ns: String,
    /// Ordered field names (the base fields defined in defrecord)
    pub fields: Vec<Symbol>,
}

impl RecordDef {
    /// Create a new record definition.
    pub fn new(name: Symbol, ns: String, fields: Vec<Symbol>) -> Self {
        RecordDef { name, ns, fields }
    }

    /// Get the fully qualified name of the record type.
    #[must_use]
    pub fn qualified_name(&self) -> String {
        format!("{}/{}", self.ns, self.name)
    }
}

/// An instance of a record type.
///
/// Records are like maps but with a defined type and set of base fields.
/// They support keyword access, assoc, and dissoc, but maintain their type
/// identity. Removing a base field via dissoc converts the record to a map.
#[derive(Clone, Debug)]
pub struct RecordInstance {
    /// The record type name (e.g., `Person`)
    pub record_type: Symbol,
    /// Namespace where the record type was defined
    pub record_ns: String,
    /// Ordered base field names (from the record definition)
    pub fields: Vec<Symbol>,
    /// All values: base fields + any extra keys added via assoc
    pub values: std::collections::HashMap<Keyword, KlujurVal>,
}

impl RecordInstance {
    /// Create a new record instance.
    pub fn new(
        record_type: Symbol,
        record_ns: String,
        fields: Vec<Symbol>,
        values: std::collections::HashMap<Keyword, KlujurVal>,
    ) -> Self {
        RecordInstance {
            record_type,
            record_ns,
            fields,
            values,
        }
    }

    /// Get a field value by keyword.
    #[must_use]
    pub fn get(&self, key: &Keyword) -> Option<&KlujurVal> {
        self.values.get(key)
    }

    /// Create a new record with an added/updated key-value pair.
    #[must_use]
    pub fn assoc(&self, key: Keyword, value: KlujurVal) -> Self {
        let mut new_values = self.values.clone();
        new_values.insert(key, value);
        RecordInstance {
            record_type: self.record_type.clone(),
            record_ns: self.record_ns.clone(),
            fields: self.fields.clone(),
            values: new_values,
        }
    }

    /// Remove a key from the record.
    ///
    /// If the key is a base field, returns a Map (record loses its type).
    /// If the key is an extra field, returns a Record.
    #[must_use]
    pub fn dissoc(&self, key: &Keyword) -> KlujurVal {
        // Check if this is a base field
        let is_base_field = self.fields.iter().any(|f| f.name() == key.name());

        if is_base_field {
            // Dissoc'ing a base field converts to a map
            let mut map = OrdMap::new();
            for (k, v) in &self.values {
                if k != key {
                    map.insert(KlujurVal::Keyword(k.clone()), v.clone());
                }
            }
            KlujurVal::Map(map, None)
        } else {
            // Dissoc'ing an extra field keeps it as a record
            let mut new_values = self.values.clone();
            new_values.remove(key);
            KlujurVal::Record(Rc::new(RecordInstance {
                record_type: self.record_type.clone(),
                record_ns: self.record_ns.clone(),
                fields: self.fields.clone(),
                values: new_values,
            }))
        }
    }

    /// Check if this is a base field of the record.
    #[must_use]
    pub fn is_base_field(&self, key: &Keyword) -> bool {
        self.fields.iter().any(|f| f.name() == key.name())
    }

    /// Get the fully qualified type name.
    #[must_use]
    pub fn qualified_type_name(&self) -> String {
        format!("{}/{}", self.record_ns, self.record_type)
    }
}

impl fmt::Display for RecordInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}{{", self.record_type)?;
        let mut first = true;

        // Print base fields first (in order)
        for field in &self.fields {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            let key = Keyword::new(field.name());
            let value = self.values.get(&key).unwrap_or(&KlujurVal::Nil);
            write!(f, ":{} {}", field.name(), value)?;
        }

        // Print extra keys (sorted for consistency)
        let mut extra_keys: Vec<_> = self
            .values
            .keys()
            .filter(|k| !self.is_base_field(k))
            .collect();
        extra_keys.sort_by(|a, b| a.name().cmp(b.name()));

        for key in extra_keys {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            let value = self.values.get(key).unwrap_or(&KlujurVal::Nil);
            write!(f, ":{} {}", key.name(), value)?;
        }

        write!(f, "}}")
    }
}

impl PartialEq for RecordInstance {
    fn eq(&self, other: &Self) -> bool {
        // Records are equal if same type and same values
        self.record_type == other.record_type
            && self.record_ns == other.record_ns
            && self.values == other.values
    }
}

impl Eq for RecordInstance {}

impl PartialOrd for RecordInstance {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RecordInstance {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.record_ns.cmp(&other.record_ns) {
            std::cmp::Ordering::Equal => match self.record_type.cmp(&other.record_type) {
                std::cmp::Ordering::Equal => {
                    // Compare values by converting to sorted vec
                    let self_entries: Vec<_> = {
                        let mut v: Vec<_> = self.values.iter().collect();
                        v.sort_by(|a, b| a.0.cmp(b.0));
                        v
                    };
                    let other_entries: Vec<_> = {
                        let mut v: Vec<_> = other.values.iter().collect();
                        v.sort_by(|a, b| a.0.cmp(b.0));
                        v
                    };
                    self_entries.cmp(&other_entries)
                }
                other => other,
            },
            other => other,
        }
    }
}

impl Hash for RecordInstance {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.record_type.hash(state);
        self.record_ns.hash(state);
        // Hash values in sorted order for consistency
        let mut entries: Vec<_> = self.values.iter().collect();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        for (k, v) in entries {
            k.hash(state);
            v.hash(state);
        }
    }
}

// ============================================================================
// Sorted Collection Types (with custom comparators)
// ============================================================================

/// A sorted map with a custom key comparator function.
///
/// Unlike the standard `Map` which uses the default `Ord` implementation,
/// `SortedMapBy` uses a user-provided comparator function to determine
/// key ordering. The comparator is stored with the collection and used
/// for all operations (get, assoc, dissoc).
#[derive(Clone)]
pub struct KlujurSortedMapBy {
    /// The comparator function for keys (takes two args, returns int or bool)
    comparator: Rc<KlujurVal>,
    /// Entries stored in sorted order by the comparator: (key, value) pairs
    entries: Rc<RefCell<Vec<(KlujurVal, KlujurVal)>>>,
    /// Optional metadata
    meta: Option<Rc<Meta>>,
}

impl KlujurSortedMapBy {
    /// Create a new empty sorted map with the given comparator.
    pub fn new(comparator: KlujurVal) -> Self {
        KlujurSortedMapBy {
            comparator: Rc::new(comparator),
            entries: Rc::new(RefCell::new(Vec::new())),
            meta: None,
        }
    }

    /// Create a sorted map with entries (assumed to be already sorted).
    pub fn from_entries(comparator: KlujurVal, entries: Vec<(KlujurVal, KlujurVal)>) -> Self {
        KlujurSortedMapBy {
            comparator: Rc::new(comparator),
            entries: Rc::new(RefCell::new(entries)),
            meta: None,
        }
    }

    /// Get the comparator function.
    #[must_use]
    pub fn comparator(&self) -> &KlujurVal {
        &self.comparator
    }

    /// Get a clone of the comparator Rc.
    #[must_use]
    pub fn comparator_rc(&self) -> Rc<KlujurVal> {
        Rc::clone(&self.comparator)
    }

    /// Get the number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.borrow().len()
    }

    /// Check if the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.borrow().is_empty()
    }

    /// Get a clone of all entries.
    #[must_use]
    pub fn entries(&self) -> Vec<(KlujurVal, KlujurVal)> {
        self.entries.borrow().clone()
    }

    /// Get a reference to the entries RefCell for external manipulation.
    #[deprecated(since = "0.2.0", note = "Use from_entries() constructor instead")]
    pub fn entries_cell(&self) -> &Rc<RefCell<Vec<(KlujurVal, KlujurVal)>>> {
        &self.entries
    }

    /// Get the metadata.
    #[must_use]
    pub fn meta(&self) -> Option<&Rc<Meta>> {
        self.meta.as_ref()
    }

    /// Create a new SortedMapBy with different metadata.
    #[must_use]
    pub fn with_meta(&self, meta: Option<Rc<Meta>>) -> Self {
        KlujurSortedMapBy {
            comparator: Rc::clone(&self.comparator),
            entries: Rc::clone(&self.entries),
            meta,
        }
    }

    /// Create a new empty map with the same comparator.
    #[must_use]
    pub fn empty(&self) -> Self {
        KlujurSortedMapBy {
            comparator: Rc::clone(&self.comparator),
            entries: Rc::new(RefCell::new(Vec::new())),
            meta: None,
        }
    }
}

impl fmt::Debug for KlujurSortedMapBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<SortedMapBy: {} entries>", self.len())
    }
}

impl fmt::Display for KlujurSortedMapBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let entries = self.entries.borrow();
        for (i, (k, v)) in entries.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{} {}", k, v)?;
        }
        write!(f, "}}")
    }
}

impl PartialEq for KlujurSortedMapBy {
    fn eq(&self, other: &Self) -> bool {
        // Identity comparison (same as Atom)
        Rc::ptr_eq(&self.entries, &other.entries)
    }
}

impl Eq for KlujurSortedMapBy {}

impl PartialOrd for KlujurSortedMapBy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurSortedMapBy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.entries) as usize;
        let other_ptr = Rc::as_ptr(&other.entries) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

impl Hash for KlujurSortedMapBy {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash by pointer address (identity-based)
        (Rc::as_ptr(&self.entries) as usize).hash(state);
    }
}

/// A sorted set with a custom comparator function.
///
/// Unlike the standard `Set` which uses the default `Ord` implementation,
/// `SortedSetBy` uses a user-provided comparator function to determine
/// element ordering. The comparator is stored with the collection and used
/// for all operations (contains?, conj, disj).
#[derive(Clone)]
pub struct KlujurSortedSetBy {
    /// The comparator function for elements (takes two args, returns int or bool)
    comparator: Rc<KlujurVal>,
    /// Elements stored in sorted order by the comparator
    elements: Rc<RefCell<Vec<KlujurVal>>>,
    /// Optional metadata
    meta: Option<Rc<Meta>>,
}

impl KlujurSortedSetBy {
    /// Create a new empty sorted set with the given comparator.
    pub fn new(comparator: KlujurVal) -> Self {
        KlujurSortedSetBy {
            comparator: Rc::new(comparator),
            elements: Rc::new(RefCell::new(Vec::new())),
            meta: None,
        }
    }

    /// Create a sorted set with elements (assumed to be already sorted and deduped).
    pub fn from_elements(comparator: KlujurVal, elements: Vec<KlujurVal>) -> Self {
        KlujurSortedSetBy {
            comparator: Rc::new(comparator),
            elements: Rc::new(RefCell::new(elements)),
            meta: None,
        }
    }

    /// Get the comparator function.
    #[must_use]
    pub fn comparator(&self) -> &KlujurVal {
        &self.comparator
    }

    /// Get a clone of the comparator Rc.
    #[must_use]
    pub fn comparator_rc(&self) -> Rc<KlujurVal> {
        Rc::clone(&self.comparator)
    }

    /// Get the number of elements.
    #[must_use]
    pub fn len(&self) -> usize {
        self.elements.borrow().len()
    }

    /// Check if the set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.elements.borrow().is_empty()
    }

    /// Get a clone of all elements.
    #[must_use]
    pub fn elements(&self) -> Vec<KlujurVal> {
        self.elements.borrow().clone()
    }

    /// Get a reference to the elements RefCell for external manipulation.
    #[deprecated(since = "0.2.0", note = "Use from_elements() constructor instead")]
    pub fn elements_cell(&self) -> &Rc<RefCell<Vec<KlujurVal>>> {
        &self.elements
    }

    /// Get the metadata.
    #[must_use]
    pub fn meta(&self) -> Option<&Rc<Meta>> {
        self.meta.as_ref()
    }

    /// Create a new SortedSetBy with different metadata.
    #[must_use]
    pub fn with_meta(&self, meta: Option<Rc<Meta>>) -> Self {
        KlujurSortedSetBy {
            comparator: Rc::clone(&self.comparator),
            elements: Rc::clone(&self.elements),
            meta,
        }
    }

    /// Create a new empty set with the same comparator.
    #[must_use]
    pub fn empty(&self) -> Self {
        KlujurSortedSetBy {
            comparator: Rc::clone(&self.comparator),
            elements: Rc::new(RefCell::new(Vec::new())),
            meta: None,
        }
    }
}

impl fmt::Debug for KlujurSortedSetBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<SortedSetBy: {} elements>", self.len())
    }
}

impl fmt::Display for KlujurSortedSetBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{{")?;
        let elements = self.elements.borrow();
        for (i, elem) in elements.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", elem)?;
        }
        write!(f, "}}")
    }
}

impl PartialEq for KlujurSortedSetBy {
    fn eq(&self, other: &Self) -> bool {
        // Identity comparison (same as Atom)
        Rc::ptr_eq(&self.elements, &other.elements)
    }
}

impl Eq for KlujurSortedSetBy {}

impl PartialOrd for KlujurSortedSetBy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurSortedSetBy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.elements) as usize;
        let other_ptr = Rc::as_ptr(&other.elements) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

impl Hash for KlujurSortedSetBy {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash by pointer address (identity-based)
        (Rc::as_ptr(&self.elements) as usize).hash(state);
    }
}

/// Metadata type: an ordered map of KlujurVal to KlujurVal.
/// Wrapped in Rc for cheap cloning and Option for zero-cost when absent.
pub type Meta = OrdMap<KlujurVal, KlujurVal>;

/// The core value type for Klujur.
///
/// All values in Klujur are represented by this enum. Values are immutable
/// and use reference counting for efficient sharing.
///
/// Types that support metadata (List, Vector, Map, Set, Symbol) have an
/// optional `Rc<Meta>` field. Metadata does not affect equality or hashing.
#[derive(Clone)]
pub enum KlujurVal {
    /// The nil value, representing nothing/absence
    Nil,
    /// Boolean true or false
    Bool(bool),
    /// 64-bit signed integer
    Int(i64),
    /// 64-bit floating point number
    Float(f64),
    /// Rational number (numerator/denominator)
    Ratio(i64, i64),
    /// Unicode character
    Char(char),
    /// Immutable string
    String(Rc<str>),
    /// Symbol (optionally namespaced identifier, with optional metadata)
    Symbol(Symbol, Option<Rc<Meta>>),
    /// Keyword (optionally namespaced, self-evaluating)
    Keyword(Keyword),
    /// Linked list (persistent, structural sharing, with optional metadata)
    List(Vector<KlujurVal>, Option<Rc<Meta>>),
    /// Indexed vector (persistent, structural sharing, with optional metadata)
    Vector(Vector<KlujurVal>, Option<Rc<Meta>>),
    /// Ordered map (persistent, structural sharing, with optional metadata)
    Map(OrdMap<KlujurVal, KlujurVal>, Option<Rc<Meta>>),
    /// Ordered set (persistent, structural sharing, with optional metadata)
    Set(OrdSet<KlujurVal>, Option<Rc<Meta>>),
    /// User-defined function (closure)
    Fn(KlujurFn),
    /// Native (Rust) function
    NativeFn(KlujurNativeFn),
    /// Macro (like fn but receives unevaluated forms)
    Macro(KlujurFn),
    /// Var (mutable reference used by def)
    Var(KlujurVar),
    /// Atom (mutable reference for application state)
    Atom(KlujurAtom),
    /// Delay (lazy computation with caching)
    Delay(KlujurDelay),
    /// Lazy sequence (deferred computation producing a sequence)
    LazySeq(KlujurLazySeq),
    /// Multimethod (runtime polymorphic dispatch)
    Multimethod(Rc<KlujurMultimethod>),
    /// Hierarchy (for type relationships in multimethods)
    Hierarchy(Rc<RefCell<KlujurHierarchy>>),
    /// Reduced value (for early termination in transducers)
    Reduced(Box<KlujurVal>),
    /// Volatile reference (lightweight mutable state for transducers)
    Volatile(KlujurVolatile),
    /// Protocol (for polymorphic dispatch)
    Protocol(KlujurProtocol),
    /// Record instance (named type with defined fields, like a typed map)
    Record(Rc<RecordInstance>),
    /// Sorted map with custom comparator
    SortedMapBy(KlujurSortedMapBy),
    /// Sorted set with custom comparator
    SortedSetBy(KlujurSortedSetBy),
    /// Custom embedded Rust type
    Custom(KlujurCustom),
}

// ============================================================================
// Function Types
// ============================================================================

/// A single arity definition for a function.
#[derive(Clone)]
pub struct FnArity {
    /// Parameter names (excluding rest param) - for simple arity matching
    pub params: Vec<Symbol>,
    /// Rest parameter name, if any
    pub rest_param: Option<Symbol>,
    /// Original parameter patterns (for destructuring support)
    /// If empty, params are used directly. If non-empty, these are the
    /// destructuring patterns corresponding to each param position.
    pub param_patterns: Vec<KlujurVal>,
    /// Original rest parameter pattern (for destructuring support)
    pub rest_pattern: Option<KlujurVal>,
    /// Function body expressions
    pub body: Vec<KlujurVal>,
}

impl FnArity {
    /// Create a new arity definition.
    pub fn new(params: Vec<Symbol>, rest_param: Option<Symbol>, body: Vec<KlujurVal>) -> Self {
        FnArity {
            params,
            rest_param,
            param_patterns: Vec::new(),
            rest_pattern: None,
            body,
        }
    }

    /// Create a new arity definition with destructuring patterns.
    pub fn with_patterns(
        params: Vec<Symbol>,
        rest_param: Option<Symbol>,
        param_patterns: Vec<KlujurVal>,
        rest_pattern: Option<KlujurVal>,
        body: Vec<KlujurVal>,
    ) -> Self {
        FnArity {
            params,
            rest_param,
            param_patterns,
            rest_pattern,
            body,
        }
    }

    /// Get the minimum number of arguments this arity accepts.
    #[must_use]
    pub fn min_arity(&self) -> usize {
        self.params.len()
    }

    /// Check if this arity can accept the given number of arguments.
    #[must_use]
    pub fn matches(&self, arg_count: usize) -> bool {
        if self.rest_param.is_some() {
            arg_count >= self.params.len()
        } else {
            arg_count == self.params.len()
        }
    }
}

/// A user-defined function (closure).
///
/// Stores one or more arities, each with parameters, body, and a type-erased
/// environment reference. The actual environment type is defined in klujur-core.
#[derive(Clone)]
pub struct KlujurFn {
    /// Function name (for error messages, optional)
    pub name: Option<Symbol>,
    /// One or more arity definitions
    pub arities: Vec<FnArity>,
    /// Captured environment (type-erased to avoid circular dependency)
    pub env: Rc<dyn Any>,
}

impl KlujurFn {
    /// Create a new single-arity function.
    ///
    /// Note: An empty body is valid in Clojure and returns `nil` when invoked.
    pub fn new(
        params: Vec<Symbol>,
        rest_param: Option<Symbol>,
        body: Vec<KlujurVal>,
        env: Rc<dyn Any>,
    ) -> Self {
        KlujurFn {
            name: None,
            arities: vec![FnArity::new(params, rest_param, body)],
            env,
        }
    }

    /// Create a new multi-arity function.
    ///
    /// # Panics (debug mode only)
    ///
    /// Debug assertions will panic if:
    /// - `arities` is empty (must have at least one arity)
    /// - Two arities have the same fixed parameter count (ambiguous dispatch)
    ///
    /// Note: Empty bodies are valid (return `nil` when invoked).
    pub fn new_multi(name: Option<Symbol>, arities: Vec<FnArity>, env: Rc<dyn Any>) -> Self {
        debug_assert!(
            !arities.is_empty(),
            "Multi-arity function must have at least one arity"
        );
        // Check for duplicate arity counts (excluding variadic)
        #[cfg(debug_assertions)]
        {
            let mut fixed_counts: Vec<usize> = arities
                .iter()
                .filter(|a| a.rest_param.is_none())
                .map(|a| a.params.len())
                .collect();
            fixed_counts.sort_unstable();
            let original_len = fixed_counts.len();
            fixed_counts.dedup();
            debug_assert!(
                fixed_counts.len() == original_len,
                "Multi-arity function has duplicate arity counts; each fixed arity must be unique"
            );
        }
        KlujurFn { name, arities, env }
    }

    /// Find the arity that matches the given argument count.
    #[must_use]
    pub fn find_arity(&self, arg_count: usize) -> Option<&FnArity> {
        // First try to find an exact match (non-variadic)
        self.arities
            .iter()
            .find(|arity| arity.rest_param.is_none() && arity.params.len() == arg_count)
            .or_else(|| {
                // Then try variadic arities
                self.arities
                    .iter()
                    .find(|arity| arity.rest_param.is_some() && arg_count >= arity.params.len())
            })
    }

    // Legacy accessors for backward compatibility with single-arity code
    /// Get parameters of the first (or only) arity.
    ///
    /// Returns `None` if the function has no arities.
    #[must_use]
    pub fn params(&self) -> Option<&[Symbol]> {
        self.arities.first().map(|a| a.params.as_slice())
    }

    /// Get rest parameter of the first (or only) arity.
    ///
    /// Returns `None` if the function has no arities.
    #[must_use]
    pub fn rest_param(&self) -> Option<&Symbol> {
        self.arities.first().and_then(|a| a.rest_param.as_ref())
    }

    /// Get body of the first (or only) arity.
    ///
    /// Returns `None` if the function has no arities.
    #[must_use]
    pub fn body(&self) -> Option<&[KlujurVal]> {
        self.arities.first().map(|a| a.body.as_slice())
    }
}

impl fmt::Debug for KlujurFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<fn>")
    }
}

impl PartialEq for KlujurFn {
    fn eq(&self, _other: &Self) -> bool {
        false // Functions are never equal
    }
}

/// A native (Rust) function.
#[derive(Clone)]
pub struct KlujurNativeFn {
    /// Function name for display (using Rc<str> to avoid memory leaks from Box::leak)
    pub name: Rc<str>,
    /// The actual function (type-erased)
    func: Rc<dyn Any>,
}

impl KlujurNativeFn {
    /// Create a new native function with a type-erased function.
    pub fn new(name: impl Into<Rc<str>>, func: Rc<dyn Any>) -> Self {
        KlujurNativeFn {
            name: name.into(),
            func,
        }
    }

    /// Get the function name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the inner function reference.
    #[must_use]
    pub fn func(&self) -> &Rc<dyn Any> {
        &self.func
    }
}

impl fmt::Debug for KlujurNativeFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<native-fn {}>", self.name)
    }
}

impl PartialEq for KlujurNativeFn {
    fn eq(&self, other: &Self) -> bool {
        // Use Rc pointer comparison for identity equality
        Rc::ptr_eq(&self.func, &other.func)
    }
}

// ============================================================================
// Var Type
// ============================================================================

use std::cell::RefCell;

/// A Var is a mutable reference to a value, typically created by `def`.
///
/// Vars are the primary mechanism for global/namespace-level bindings in Clojure.
/// They have:
/// - A namespace (optional, for display)
/// - A name (the symbol bound to)
/// - A root value (the current value)
/// - A dynamic flag (for thread-local bindings)
/// - Optional metadata (mutable via alter-meta!/reset-meta!)
#[derive(Clone)]
pub struct KlujurVar {
    /// Namespace name (for qualified display)
    pub ns: Option<String>,
    /// Var name
    pub name: String,
    /// The root binding (mutable)
    root: Rc<RefCell<KlujurVal>>,
    /// Whether this var supports dynamic (thread-local) binding
    dynamic: Rc<RefCell<bool>>,
    /// Var metadata (mutable, for doc strings, arglists, etc.)
    meta: Rc<RefCell<Option<Meta>>>,
}

impl KlujurVar {
    /// Create a new Var with a value.
    pub fn new(name: String, value: KlujurVal) -> Self {
        KlujurVar {
            ns: None,
            name,
            root: Rc::new(RefCell::new(value)),
            dynamic: Rc::new(RefCell::new(false)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Create a new Var with namespace.
    pub fn new_with_ns(ns: String, name: String, value: KlujurVal) -> Self {
        KlujurVar {
            ns: Some(ns),
            name,
            root: Rc::new(RefCell::new(value)),
            dynamic: Rc::new(RefCell::new(false)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Get the current value (deref).
    /// Note: Thread-local bindings are checked in klujur-core, not here,
    /// to avoid circular dependency. This only returns the root value.
    #[must_use]
    pub fn deref(&self) -> KlujurVal {
        self.root.borrow().clone()
    }

    /// Set the root value.
    pub fn set_root(&self, value: KlujurVal) {
        *self.root.borrow_mut() = value;
    }

    /// Check if this var is dynamic.
    #[must_use]
    pub fn is_dynamic(&self) -> bool {
        *self.dynamic.borrow()
    }

    /// Check if this var is public (not marked with :private metadata).
    ///
    /// A var is public unless its metadata contains `:private true`.
    /// This mirrors Clojure's Var.isPublic() method.
    #[must_use]
    pub fn is_public(&self) -> bool {
        let meta_ref = self.meta.borrow();
        if let Some(ref meta) = *meta_ref {
            // Check if :private key exists and is truthy
            let private_key = KlujurVal::Keyword(crate::keyword::Keyword::new("private"));
            if let Some(val) = meta.get(&private_key) {
                return !val.is_truthy();
            }
        }
        true // No metadata or no :private key means public
    }

    /// Set the dynamic flag.
    pub fn set_dynamic(&self, dynamic: bool) {
        *self.dynamic.borrow_mut() = dynamic;
    }

    /// Get the fully qualified name.
    #[must_use]
    pub fn qualified_name(&self) -> String {
        match &self.ns {
            Some(ns) => format!("{}/{}", ns, self.name),
            None => self.name.clone(),
        }
    }

    /// Get the var's metadata.
    #[must_use]
    pub fn meta(&self) -> Option<Meta> {
        self.meta.borrow().clone()
    }

    /// Set the var's metadata (reset-meta!).
    pub fn set_meta(&self, meta: Option<Meta>) {
        *self.meta.borrow_mut() = meta;
    }

    /// Alter the var's metadata by applying a function.
    /// Returns the new metadata value.
    pub fn alter_meta<F>(&self, f: F) -> Option<Meta>
    where
        F: FnOnce(Option<Meta>) -> Option<Meta>,
    {
        let mut meta_ref = self.meta.borrow_mut();
        let new_meta = f(meta_ref.clone());
        *meta_ref = new_meta.clone();
        new_meta
    }
}

impl fmt::Debug for KlujurVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#'{}", self.qualified_name())
    }
}

impl fmt::Display for KlujurVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#'{}", self.qualified_name())
    }
}

impl PartialEq for KlujurVar {
    fn eq(&self, other: &Self) -> bool {
        // Vars are equal if they point to the same root
        Rc::ptr_eq(&self.root, &other.root)
    }
}

impl Eq for KlujurVar {}

impl PartialOrd for KlujurVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.qualified_name().cmp(&other.qualified_name())
    }
}

// ============================================================================
// Atom Type
// ============================================================================

/// A Clojure-style atom for mutable state management.
///
/// Atoms provide synchronous, uncoordinated, atomic state management.
/// They support validators and watchers for state validation and observation.
#[derive(Clone)]
pub struct KlujurAtom {
    /// The current value (mutable)
    value: Rc<RefCell<KlujurVal>>,
    /// Optional validator function
    validator: Rc<RefCell<Option<KlujurVal>>>,
    /// Watchers: key -> watch function
    watches: Rc<RefCell<OrdMap<KlujurVal, KlujurVal>>>,
}

impl KlujurAtom {
    /// Create a new Atom with an initial value.
    pub fn new(value: KlujurVal) -> Self {
        KlujurAtom {
            value: Rc::new(RefCell::new(value)),
            validator: Rc::new(RefCell::new(None)),
            watches: Rc::new(RefCell::new(OrdMap::new())),
        }
    }

    /// Get the current value (deref).
    #[must_use]
    pub fn deref(&self) -> KlujurVal {
        self.value.borrow().clone()
    }

    /// Reset the atom to a new value, returning the new value.
    /// Returns Err if validator rejects the value.
    pub fn reset(&self, new_val: KlujurVal) -> Result<KlujurVal, String> {
        // Note: Validation should be done by the caller in klujur-core
        // since it requires calling Klujur functions
        let old_val = self.value.borrow().clone();
        *self.value.borrow_mut() = new_val.clone();
        Ok(old_val)
    }

    /// Reset and return [old new] pair.
    pub fn reset_vals(&self, new_val: KlujurVal) -> (KlujurVal, KlujurVal) {
        let old_val = self.value.borrow().clone();
        *self.value.borrow_mut() = new_val.clone();
        (old_val, new_val)
    }

    /// Set the value directly (used by swap! after computing new value).
    pub fn set_value(&self, new_val: KlujurVal) {
        *self.value.borrow_mut() = new_val;
    }

    /// Compare and set: only update if current value equals old_val.
    pub fn compare_and_set(&self, old_val: &KlujurVal, new_val: KlujurVal) -> bool {
        let current = self.value.borrow();
        if *current == *old_val {
            drop(current);
            *self.value.borrow_mut() = new_val;
            true
        } else {
            false
        }
    }

    /// Get the validator function.
    #[must_use]
    pub fn get_validator(&self) -> Option<KlujurVal> {
        self.validator.borrow().clone()
    }

    /// Set the validator function.
    pub fn set_validator(&self, f: Option<KlujurVal>) {
        *self.validator.borrow_mut() = f;
    }

    /// Add a watch function.
    pub fn add_watch(&self, key: KlujurVal, f: KlujurVal) {
        self.watches.borrow_mut().insert(key, f);
    }

    /// Remove a watch function.
    pub fn remove_watch(&self, key: &KlujurVal) {
        self.watches.borrow_mut().remove(key);
    }

    /// Get all watches (for calling from klujur-core).
    #[must_use]
    pub fn get_watches(&self) -> OrdMap<KlujurVal, KlujurVal> {
        self.watches.borrow().clone()
    }
}

impl fmt::Debug for KlujurAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Atom: {:?}>", self.value.borrow())
    }
}

impl fmt::Display for KlujurAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Atom: {}>", self.value.borrow())
    }
}

impl PartialEq for KlujurAtom {
    fn eq(&self, other: &Self) -> bool {
        // Atoms are equal if they point to the same value cell
        Rc::ptr_eq(&self.value, &other.value)
    }
}

impl Eq for KlujurAtom {}

impl PartialOrd for KlujurAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.value) as usize;
        let other_ptr = Rc::as_ptr(&other.value) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

// ============================================================================
// Volatile Type
// ============================================================================

/// A Clojure-style volatile for lightweight mutable state.
///
/// Volatiles are similar to atoms but without coordination guarantees.
/// They are intended for use in transducers and other single-threaded
/// contexts where atomic operations are not required.
#[derive(Clone)]
pub struct KlujurVolatile {
    /// The current value (mutable)
    value: Rc<RefCell<KlujurVal>>,
}

impl KlujurVolatile {
    /// Create a new Volatile with an initial value.
    pub fn new(value: KlujurVal) -> Self {
        KlujurVolatile {
            value: Rc::new(RefCell::new(value)),
        }
    }

    /// Get the current value (deref).
    #[must_use]
    pub fn deref(&self) -> KlujurVal {
        self.value.borrow().clone()
    }

    /// Reset the volatile to a new value, returning the new value.
    pub fn reset(&self, new_val: KlujurVal) -> KlujurVal {
        *self.value.borrow_mut() = new_val.clone();
        new_val
    }

    /// Swap the volatile's value, applying a function to the current value.
    /// Returns the new value.
    pub fn swap<F>(&self, f: F) -> KlujurVal
    where
        F: FnOnce(KlujurVal) -> KlujurVal,
    {
        let old_val = self.value.borrow().clone();
        let new_val = f(old_val);
        *self.value.borrow_mut() = new_val.clone();
        new_val
    }

    /// Get a raw pointer for identity-based operations (hashing, comparison).
    #[must_use]
    pub fn as_ptr(&self) -> *const RefCell<KlujurVal> {
        Rc::as_ptr(&self.value)
    }

    /// Get mutable access to the underlying value cell.
    /// Used by vswap! which needs to compute new value from old.
    #[deprecated(since = "0.2.0", note = "Use swap() instead")]
    pub fn value_cell(&self) -> &Rc<RefCell<KlujurVal>> {
        &self.value
    }
}

impl fmt::Debug for KlujurVolatile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Volatile: {:?}>", self.value.borrow())
    }
}

impl fmt::Display for KlujurVolatile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Volatile: {}>", self.value.borrow())
    }
}

impl PartialEq for KlujurVolatile {
    fn eq(&self, other: &Self) -> bool {
        // Volatiles are equal if they point to the same value cell
        Rc::ptr_eq(&self.value, &other.value)
    }
}

impl Eq for KlujurVolatile {}

impl PartialOrd for KlujurVolatile {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurVolatile {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.value) as usize;
        let other_ptr = Rc::as_ptr(&other.value) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

// ============================================================================
// Delay Type
// ============================================================================

/// A Clojure-style delay for lazy computation with caching.
///
/// The body is evaluated at most once when first dereferenced,
/// and the result is cached for subsequent accesses.
#[derive(Clone)]
pub struct KlujurDelay {
    /// The thunk (unevaluated function) or cached value
    /// None: unevaluated, contains a fn to call
    /// Some: evaluated, contains the cached result
    state: Rc<RefCell<DelayState>>,
}

/// Internal state of a delay
#[derive(Clone)]
enum DelayState {
    /// Not yet evaluated - contains the body as a thunk function
    Pending(KlujurVal),
    /// Already evaluated - contains the cached result
    Realized(KlujurVal),
}

impl KlujurDelay {
    /// Create a new Delay with a thunk (a zero-arg function to call).
    pub fn new(thunk: KlujurVal) -> Self {
        KlujurDelay {
            state: Rc::new(RefCell::new(DelayState::Pending(thunk))),
        }
    }

    /// Check if the delay has been realized.
    #[must_use]
    pub fn is_realized(&self) -> bool {
        matches!(*self.state.borrow(), DelayState::Realized(_))
    }

    /// Get the thunk if pending, or None if already realized.
    #[must_use]
    pub fn get_thunk(&self) -> Option<KlujurVal> {
        match &*self.state.borrow() {
            DelayState::Pending(thunk) => Some(thunk.clone()),
            DelayState::Realized(_) => None,
        }
    }

    /// Get the cached value if realized, or None if pending.
    #[must_use]
    pub fn get_cached(&self) -> Option<KlujurVal> {
        match &*self.state.borrow() {
            DelayState::Pending(_) => None,
            DelayState::Realized(val) => Some(val.clone()),
        }
    }

    /// Set the realized value (called after evaluating the thunk).
    pub fn set_realized(&self, val: KlujurVal) {
        *self.state.borrow_mut() = DelayState::Realized(val);
    }
}

impl fmt::Debug for KlujurDelay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.state.borrow() {
            DelayState::Pending(_) => write!(f, "#<Delay: pending>"),
            DelayState::Realized(val) => write!(f, "#<Delay: {:?}>", val),
        }
    }
}

impl fmt::Display for KlujurDelay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.state.borrow() {
            DelayState::Pending(_) => write!(f, "#<Delay: pending>"),
            DelayState::Realized(val) => write!(f, "#<Delay: {}>", val),
        }
    }
}

impl PartialEq for KlujurDelay {
    fn eq(&self, other: &Self) -> bool {
        // Delays are equal if they point to the same state
        Rc::ptr_eq(&self.state, &other.state)
    }
}

impl Eq for KlujurDelay {}

impl PartialOrd for KlujurDelay {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurDelay {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.state) as usize;
        let other_ptr = Rc::as_ptr(&other.state) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

// ============================================================================
// Lazy Sequence Type
// ============================================================================

/// A Clojure-style lazy sequence.
///
/// Lazy sequences defer computation until elements are actually needed.
/// When forced, the thunk produces either:
/// - Empty (nil/empty sequence)
/// - Cons(first, rest) where rest is another lazy seq or list
///
/// Results are cached after first evaluation.
#[derive(Clone)]
pub struct KlujurLazySeq {
    /// The internal state (pending thunk or realized result)
    state: Rc<RefCell<LazySeqState>>,
}

/// Internal state of a lazy sequence
#[derive(Clone)]
pub enum LazySeqState {
    /// Not yet evaluated - contains a zero-arg function to call
    Pending(KlujurFn),
    /// Already evaluated - contains the result
    Realized(SeqResult),
}

/// Result of forcing a lazy sequence
#[derive(Clone)]
pub enum SeqResult {
    /// Empty sequence (nil)
    Empty,
    /// Cons cell: first element and rest of sequence
    Cons(KlujurVal, KlujurVal),
}

impl KlujurLazySeq {
    /// Create a new lazy sequence with a thunk (a zero-arg function to call).
    pub fn new(thunk: KlujurFn) -> Self {
        KlujurLazySeq {
            state: Rc::new(RefCell::new(LazySeqState::Pending(thunk))),
        }
    }

    /// Create a realized lazy sequence from a cons cell (first and rest).
    /// This is used by `cons` to efficiently prepend to lazy sequences.
    pub fn from_cons(first: KlujurVal, rest: KlujurVal) -> Self {
        KlujurLazySeq {
            state: Rc::new(RefCell::new(LazySeqState::Realized(SeqResult::Cons(
                first, rest,
            )))),
        }
    }

    /// Check if the lazy sequence has been realized.
    #[must_use]
    pub fn is_realized(&self) -> bool {
        matches!(*self.state.borrow(), LazySeqState::Realized(_))
    }

    /// Get the thunk if pending, or None if already realized.
    #[must_use]
    pub fn get_thunk(&self) -> Option<KlujurFn> {
        match &*self.state.borrow() {
            LazySeqState::Pending(thunk) => Some(thunk.clone()),
            LazySeqState::Realized(_) => None,
        }
    }

    /// Get the cached result if realized, or None if pending.
    #[must_use]
    pub fn get_cached(&self) -> Option<SeqResult> {
        match &*self.state.borrow() {
            LazySeqState::Pending(_) => None,
            LazySeqState::Realized(result) => Some(result.clone()),
        }
    }

    /// Set the realized result (called after evaluating the thunk).
    pub fn set_realized(&self, result: SeqResult) {
        *self.state.borrow_mut() = LazySeqState::Realized(result);
    }

    /// Get a reference to the internal state for external forcing logic.
    #[must_use]
    pub fn state(&self) -> &Rc<RefCell<LazySeqState>> {
        &self.state
    }
}

impl fmt::Debug for KlujurLazySeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.state.borrow() {
            LazySeqState::Pending(_) => write!(f, "#<LazySeq: pending>"),
            LazySeqState::Realized(SeqResult::Empty) => write!(f, "()"),
            LazySeqState::Realized(SeqResult::Cons(first, rest)) => {
                write!(f, "({:?} . {:?})", first, rest)
            }
        }
    }
}

impl fmt::Display for KlujurLazySeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // For display, we show as much as we can without forcing unrealized portions
        let state = self.state.borrow();
        match &*state {
            LazySeqState::Pending(_) => write!(f, "(...)"),
            LazySeqState::Realized(SeqResult::Empty) => write!(f, "()"),
            LazySeqState::Realized(SeqResult::Cons(first, rest)) => {
                // Display realized elements, stopping at unrealized portions or print-length
                write!(f, "({}", first)?;
                let mut current = rest.clone();
                drop(state); // Release borrow before loop
                let mut count = 1;
                // Use *print-length* if set, otherwise default to 32 for lazy seqs
                let max_display = get_print_length().unwrap_or(32);

                loop {
                    if count >= max_display {
                        write!(f, " ...")?;
                        break;
                    }
                    match current {
                        KlujurVal::Nil => break,
                        KlujurVal::List(ref items, _) if items.is_empty() => break,
                        KlujurVal::List(ref items, _) => {
                            for item in items.iter() {
                                if count >= max_display {
                                    write!(f, " ...")?;
                                    break;
                                }
                                write!(f, " {}", item)?;
                                count += 1;
                            }
                            break;
                        }
                        KlujurVal::LazySeq(ref ls) => {
                            let ls_state = ls.state.borrow();
                            match &*ls_state {
                                LazySeqState::Pending(_) => {
                                    write!(f, " ...")?;
                                    break;
                                }
                                LazySeqState::Realized(SeqResult::Empty) => break,
                                LazySeqState::Realized(SeqResult::Cons(f_elem, r)) => {
                                    write!(f, " {}", f_elem)?;
                                    count += 1;
                                    let next = r.clone();
                                    drop(ls_state);
                                    current = next;
                                }
                            }
                        }
                        _ => {
                            // Unexpected rest type, just show what we have
                            write!(f, " . {}", current)?;
                            break;
                        }
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl PartialEq for KlujurLazySeq {
    fn eq(&self, other: &Self) -> bool {
        // Lazy seqs are equal if they point to the same state
        Rc::ptr_eq(&self.state, &other.state)
    }
}

impl Eq for KlujurLazySeq {}

impl PartialOrd for KlujurLazySeq {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurLazySeq {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.state) as usize;
        let other_ptr = Rc::as_ptr(&other.state) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

// ============================================================================
// Multimethod Type
// ============================================================================

use std::collections::HashMap;

/// A Clojure-style multimethod for runtime polymorphic dispatch.
///
/// Multimethods dispatch on the result of calling a dispatch function
/// on the arguments, looking up the appropriate method in a method table.
#[derive(Clone)]
pub struct KlujurMultimethod {
    /// Multimethod name (for error messages)
    pub name: Symbol,
    /// Dispatch function - called on args to get dispatch value
    pub dispatch_fn: Rc<KlujurVal>,
    /// Method table: dispatch value -> method function
    pub methods: Rc<RefCell<HashMap<KlujurVal, KlujurVal>>>,
    /// Default method (for :default dispatch value)
    pub default: Rc<RefCell<Option<KlujurVal>>>,
    /// Preferences for ambiguous dispatch (pair -> true means prefer first)
    pub preferences: Rc<RefCell<HashMap<(KlujurVal, KlujurVal), bool>>>,
    /// Optional hierarchy for isa?-based dispatch
    pub hierarchy: Option<Rc<RefCell<KlujurHierarchy>>>,
}

impl KlujurMultimethod {
    /// Create a new multimethod with a name and dispatch function.
    pub fn new(name: Symbol, dispatch_fn: KlujurVal) -> Self {
        KlujurMultimethod {
            name,
            dispatch_fn: Rc::new(dispatch_fn),
            methods: Rc::new(RefCell::new(HashMap::new())),
            default: Rc::new(RefCell::new(None)),
            preferences: Rc::new(RefCell::new(HashMap::new())),
            hierarchy: None,
        }
    }

    /// Create a new multimethod with a hierarchy for isa?-based dispatch.
    pub fn with_hierarchy(
        name: Symbol,
        dispatch_fn: KlujurVal,
        hierarchy: Rc<RefCell<KlujurHierarchy>>,
    ) -> Self {
        KlujurMultimethod {
            name,
            dispatch_fn: Rc::new(dispatch_fn),
            methods: Rc::new(RefCell::new(HashMap::new())),
            default: Rc::new(RefCell::new(None)),
            preferences: Rc::new(RefCell::new(HashMap::new())),
            hierarchy: Some(hierarchy),
        }
    }

    /// Set the hierarchy for this multimethod.
    pub fn set_hierarchy(&mut self, hierarchy: Option<Rc<RefCell<KlujurHierarchy>>>) {
        self.hierarchy = hierarchy;
    }

    /// Add a method for a dispatch value.
    /// If dispatch_val is the keyword :default, sets the default method.
    pub fn add_method(&self, dispatch_val: KlujurVal, method: KlujurVal) {
        if let KlujurVal::Keyword(kw) = &dispatch_val
            && kw.name() == "default"
            && kw.namespace().is_none()
        {
            *self.default.borrow_mut() = Some(method);
            return;
        }
        self.methods.borrow_mut().insert(dispatch_val, method);
    }

    /// Remove a method for a dispatch value.
    pub fn remove_method(&self, dispatch_val: &KlujurVal) {
        self.methods.borrow_mut().remove(dispatch_val);
    }

    /// Get the method for a dispatch value.
    /// Uses hierarchy-based lookup if a hierarchy is set, then falls back to default.
    #[must_use]
    pub fn get_method(&self, dispatch_val: &KlujurVal) -> Option<KlujurVal> {
        // First try exact match
        if let Some(method) = self.methods.borrow().get(dispatch_val).cloned() {
            return Some(method);
        }

        // Try hierarchy-based lookup if available
        if let Some(ref hierarchy) = self.hierarchy {
            let h = hierarchy.borrow();
            let methods = self.methods.borrow();
            let prefs = self.preferences.borrow();

            if let Some((_, method)) = h.find_best_method(dispatch_val, &methods, &prefs) {
                return Some(method);
            }
        }

        // Fall back to default
        self.default.borrow().clone()
    }

    /// Get all methods as a map.
    #[must_use]
    pub fn get_methods(&self) -> HashMap<KlujurVal, KlujurVal> {
        self.methods.borrow().clone()
    }

    /// Set a preference: prefer x over y for ambiguous dispatch.
    pub fn prefer_method(&self, preferred: KlujurVal, other: KlujurVal) {
        self.preferences
            .borrow_mut()
            .insert((preferred, other), true);
    }

    /// Get all preferences as a map: preferred -> #{other-vals...}
    #[must_use]
    pub fn get_prefers(&self) -> HashMap<KlujurVal, OrdSet<KlujurVal>> {
        let prefs = self.preferences.borrow();
        let mut result: HashMap<KlujurVal, OrdSet<KlujurVal>> = HashMap::new();
        for (preferred, other) in prefs.keys() {
            result
                .entry(preferred.clone())
                .or_default()
                .insert(other.clone());
        }
        result
    }

    /// Remove all methods from this multimethod.
    pub fn clear_methods(&self) {
        self.methods.borrow_mut().clear();
        *self.default.borrow_mut() = None;
    }
}

impl fmt::Debug for KlujurMultimethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Multimethod {}>", self.name)
    }
}

impl fmt::Display for KlujurMultimethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Multimethod {}>", self.name)
    }
}

impl PartialEq for KlujurMultimethod {
    fn eq(&self, other: &Self) -> bool {
        // Multimethods are equal if they point to the same method table
        Rc::ptr_eq(&self.methods, &other.methods)
    }
}

impl Eq for KlujurMultimethod {}

impl PartialOrd for KlujurMultimethod {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurMultimethod {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.methods) as usize;
        let other_ptr = Rc::as_ptr(&other.methods) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

impl KlujurVal {
    /// Create a nil value
    #[must_use]
    pub fn nil() -> Self {
        KlujurVal::Nil
    }

    /// Create a boolean value
    #[must_use]
    pub fn bool(b: bool) -> Self {
        KlujurVal::Bool(b)
    }

    /// Create an integer value
    #[must_use]
    pub fn int(n: i64) -> Self {
        KlujurVal::Int(n)
    }

    /// Create a float value
    #[must_use]
    pub fn float(n: f64) -> Self {
        KlujurVal::Float(n)
    }

    /// Create a ratio value, reducing to lowest terms.
    /// Returns `None` if denominator is zero.
    #[must_use]
    pub fn try_ratio(num: i64, den: i64) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let g = gcd(num.abs(), den.abs());
        let (num, den) = if den < 0 {
            (-num / g, -den / g)
        } else {
            (num / g, den / g)
        };
        if den == 1 {
            Some(KlujurVal::Int(num))
        } else {
            Some(KlujurVal::Ratio(num, den))
        }
    }

    /// Create a ratio value, reducing to lowest terms.
    /// Panics if denominator is zero.
    #[must_use]
    pub fn ratio(num: i64, den: i64) -> Self {
        Self::try_ratio(num, den).expect("Division by zero in ratio")
    }

    /// Create a character value
    #[must_use]
    pub fn char(c: char) -> Self {
        KlujurVal::Char(c)
    }

    /// Create a string value
    #[must_use]
    pub fn string(s: impl Into<Rc<str>>) -> Self {
        KlujurVal::String(s.into())
    }

    /// Create a symbol value
    #[must_use]
    pub fn symbol(sym: Symbol) -> Self {
        KlujurVal::Symbol(sym, None)
    }

    /// Create a symbol value with metadata
    #[must_use]
    pub fn symbol_with_meta(sym: Symbol, meta: Rc<Meta>) -> Self {
        KlujurVal::Symbol(sym, Some(meta))
    }

    /// Create a keyword value
    #[must_use]
    pub fn keyword(kw: Keyword) -> Self {
        KlujurVal::Keyword(kw)
    }

    /// Create an empty list
    #[must_use]
    pub fn empty_list() -> Self {
        KlujurVal::List(Vector::new(), None)
    }

    /// Create a list from elements
    #[must_use]
    pub fn list(elements: Vec<KlujurVal>) -> Self {
        KlujurVal::List(elements.into_iter().collect(), None)
    }

    /// Create a list from elements with metadata
    #[must_use]
    pub fn list_with_meta(elements: Vec<KlujurVal>, meta: Rc<Meta>) -> Self {
        KlujurVal::List(elements.into_iter().collect(), Some(meta))
    }

    /// Create an empty vector
    #[must_use]
    pub fn empty_vector() -> Self {
        KlujurVal::Vector(Vector::new(), None)
    }

    /// Create a vector from elements
    #[must_use]
    pub fn vector(elements: Vec<KlujurVal>) -> Self {
        KlujurVal::Vector(elements.into_iter().collect(), None)
    }

    /// Create a vector from elements with metadata
    #[must_use]
    pub fn vector_with_meta(elements: Vec<KlujurVal>, meta: Rc<Meta>) -> Self {
        KlujurVal::Vector(elements.into_iter().collect(), Some(meta))
    }

    /// Create an empty map
    #[must_use]
    pub fn empty_map() -> Self {
        KlujurVal::Map(OrdMap::new(), None)
    }

    /// Create a map from key-value pairs
    #[must_use]
    pub fn map(pairs: Vec<(KlujurVal, KlujurVal)>) -> Self {
        KlujurVal::Map(pairs.into_iter().collect(), None)
    }

    /// Create a map from key-value pairs with metadata
    #[must_use]
    pub fn map_with_meta(pairs: Vec<(KlujurVal, KlujurVal)>, meta: Rc<Meta>) -> Self {
        KlujurVal::Map(pairs.into_iter().collect(), Some(meta))
    }

    /// Create an empty set
    #[must_use]
    pub fn empty_set() -> Self {
        KlujurVal::Set(OrdSet::new(), None)
    }

    /// Create a set from elements
    #[must_use]
    pub fn set(elements: Vec<KlujurVal>) -> Self {
        KlujurVal::Set(elements.into_iter().collect(), None)
    }

    /// Create a set from elements with metadata
    #[must_use]
    pub fn set_with_meta(elements: Vec<KlujurVal>, meta: Rc<Meta>) -> Self {
        KlujurVal::Set(elements.into_iter().collect(), Some(meta))
    }

    /// Check if this value is nil
    #[must_use]
    pub fn is_nil(&self) -> bool {
        matches!(self, KlujurVal::Nil)
    }

    /// Check if this value is truthy (not nil and not false)
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        !matches!(self, KlujurVal::Nil | KlujurVal::Bool(false))
    }

    /// Get the type name as a string
    #[must_use]
    pub fn type_name(&self) -> &'static str {
        match self {
            KlujurVal::Nil => "nil",
            KlujurVal::Bool(_) => "bool",
            KlujurVal::Int(_) => "int",
            KlujurVal::Float(_) => "float",
            KlujurVal::Ratio(_, _) => "ratio",
            KlujurVal::Char(_) => "char",
            KlujurVal::String(_) => "string",
            KlujurVal::Symbol(_, _) => "symbol",
            KlujurVal::Keyword(_) => "keyword",
            KlujurVal::List(_, _) => "list",
            KlujurVal::Vector(_, _) => "vector",
            KlujurVal::Map(_, _) => "map",
            KlujurVal::Set(_, _) => "set",
            KlujurVal::Fn(_) => "fn",
            KlujurVal::NativeFn(_) => "fn",
            KlujurVal::Macro(_) => "macro",
            KlujurVal::Var(_) => "var",
            KlujurVal::Atom(_) => "atom",
            KlujurVal::Delay(_) => "delay",
            KlujurVal::LazySeq(_) => "lazy-seq",
            KlujurVal::Multimethod(_) => "multimethod",
            KlujurVal::Hierarchy(_) => "hierarchy",
            KlujurVal::Reduced(_) => "reduced",
            KlujurVal::Volatile(_) => "volatile",
            KlujurVal::Protocol(_) => "protocol",
            KlujurVal::Record(_) => "record",
            KlujurVal::SortedMapBy(_) => "sorted-map",
            KlujurVal::SortedSetBy(_) => "sorted-set",
            KlujurVal::Custom(c) => c.type_name(),
        }
    }

    /// Get the type key for protocol dispatch.
    ///
    /// This returns a TypeKey that can be used to look up protocol
    /// implementations for this value's type.
    #[must_use]
    pub fn type_key(&self) -> TypeKey {
        match self {
            KlujurVal::Nil => TypeKey::Nil,
            KlujurVal::Bool(_) => TypeKey::Bool,
            KlujurVal::Int(_) => TypeKey::Int,
            KlujurVal::Float(_) => TypeKey::Float,
            KlujurVal::Ratio(_, _) => TypeKey::Ratio,
            KlujurVal::Char(_) => TypeKey::Char,
            KlujurVal::String(_) => TypeKey::String,
            KlujurVal::Symbol(_, _) => TypeKey::Symbol,
            KlujurVal::Keyword(_) => TypeKey::Keyword,
            KlujurVal::List(_, _) => TypeKey::List,
            KlujurVal::Vector(_, _) => TypeKey::Vector,
            KlujurVal::Map(_, _) => TypeKey::Map,
            KlujurVal::Set(_, _) => TypeKey::Set,
            KlujurVal::Fn(_) | KlujurVal::NativeFn(_) | KlujurVal::Macro(_) => TypeKey::Fn,
            KlujurVal::Var(_) => TypeKey::Var,
            KlujurVal::Atom(_) => TypeKey::Atom,
            KlujurVal::Delay(_) => TypeKey::Delay,
            KlujurVal::LazySeq(_) => TypeKey::LazySeq,
            KlujurVal::Multimethod(_) => TypeKey::Multimethod,
            KlujurVal::Hierarchy(_) => TypeKey::Hierarchy,
            KlujurVal::Reduced(_) => TypeKey::Reduced,
            KlujurVal::Volatile(_) => TypeKey::Volatile,
            KlujurVal::Protocol(_) => TypeKey::Fn, // Protocols dispatch as Fn type
            KlujurVal::Record(r) => TypeKey::Record(r.record_type.clone()),
            KlujurVal::SortedMapBy(_) => TypeKey::SortedMapBy,
            KlujurVal::SortedSetBy(_) => TypeKey::SortedSetBy,
            KlujurVal::Custom(c) => TypeKey::Custom(c.type_name()),
        }
    }

    /// Create an atom value
    pub fn atom(value: KlujurVal) -> Self {
        KlujurVal::Atom(KlujurAtom::new(value))
    }

    /// Create a delay value with a thunk
    pub fn delay(thunk: KlujurVal) -> Self {
        KlujurVal::Delay(KlujurDelay::new(thunk))
    }

    /// Create a lazy sequence value with a thunk
    pub fn lazy_seq(thunk: KlujurFn) -> Self {
        KlujurVal::LazySeq(KlujurLazySeq::new(thunk))
    }

    /// Create a new hierarchy value
    pub fn hierarchy() -> Self {
        KlujurVal::Hierarchy(Rc::new(RefCell::new(KlujurHierarchy::new())))
    }

    /// Create a hierarchy value from an existing hierarchy
    pub fn from_hierarchy(h: Rc<RefCell<KlujurHierarchy>>) -> Self {
        KlujurVal::Hierarchy(h)
    }

    /// Create a reduced value (for transducer early termination)
    pub fn reduced(value: KlujurVal) -> Self {
        KlujurVal::Reduced(Box::new(value))
    }

    /// Create a volatile reference
    pub fn volatile(value: KlujurVal) -> Self {
        KlujurVal::Volatile(KlujurVolatile::new(value))
    }

    /// Create a protocol value
    pub fn protocol(protocol: Protocol) -> Self {
        KlujurVal::Protocol(KlujurProtocol::new(protocol))
    }

    /// Create a protocol value from an existing Rc<Protocol>
    pub fn from_protocol(protocol: Rc<Protocol>) -> Self {
        KlujurVal::Protocol(KlujurProtocol(protocol))
    }

    /// Create a record value from a RecordInstance
    pub fn record(instance: RecordInstance) -> Self {
        KlujurVal::Record(Rc::new(instance))
    }

    /// Create a record value from an existing Rc<RecordInstance>
    pub fn from_record(instance: Rc<RecordInstance>) -> Self {
        KlujurVal::Record(instance)
    }

    /// Create a custom value wrapping an arbitrary Rust type.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let my_data = MyData { value: 42 };
    /// let val = KlujurVal::custom(my_data);
    /// ```
    pub fn custom<T: CustomType + 'static>(value: T) -> Self {
        KlujurVal::Custom(KlujurCustom::new(value))
    }

    /// Try to downcast a custom value to a specific type.
    ///
    /// Returns `None` if this is not a `Custom` variant or if the type doesn't match.
    pub fn downcast_custom<T: 'static>(&self) -> Option<&T> {
        match self {
            KlujurVal::Custom(c) => c.downcast_ref::<T>(),
            _ => None,
        }
    }

    /// Create a sorted map with a custom comparator
    pub fn sorted_map_by(comparator: KlujurVal) -> Self {
        KlujurVal::SortedMapBy(KlujurSortedMapBy::new(comparator))
    }

    /// Create a sorted set with a custom comparator
    pub fn sorted_set_by(comparator: KlujurVal) -> Self {
        KlujurVal::SortedSetBy(KlujurSortedSetBy::new(comparator))
    }

    /// Get the metadata of this value, if any.
    /// Returns None for types that don't support metadata.
    #[must_use]
    pub fn meta(&self) -> Option<&Rc<Meta>> {
        match self {
            KlujurVal::Symbol(_, meta) => meta.as_ref(),
            KlujurVal::List(_, meta) => meta.as_ref(),
            KlujurVal::Vector(_, meta) => meta.as_ref(),
            KlujurVal::Map(_, meta) => meta.as_ref(),
            KlujurVal::Set(_, meta) => meta.as_ref(),
            KlujurVal::SortedMapBy(sm) => sm.meta(),
            KlujurVal::SortedSetBy(ss) => ss.meta(),
            _ => None,
        }
    }

    /// Returns true if this value type supports metadata.
    #[must_use]
    pub fn supports_meta(&self) -> bool {
        matches!(
            self,
            KlujurVal::Symbol(_, _)
                | KlujurVal::List(_, _)
                | KlujurVal::Vector(_, _)
                | KlujurVal::Map(_, _)
                | KlujurVal::Set(_, _)
                | KlujurVal::SortedMapBy(_)
                | KlujurVal::SortedSetBy(_)
        )
    }

    /// Return a new value with the given metadata.
    /// Returns None if the value type doesn't support metadata.
    #[must_use]
    pub fn with_meta(&self, meta: Option<Rc<Meta>>) -> Option<KlujurVal> {
        match self {
            KlujurVal::Symbol(sym, _) => Some(KlujurVal::Symbol(sym.clone(), meta)),
            KlujurVal::List(items, _) => Some(KlujurVal::List(items.clone(), meta)),
            KlujurVal::Vector(items, _) => Some(KlujurVal::Vector(items.clone(), meta)),
            KlujurVal::Map(m, _) => Some(KlujurVal::Map(m.clone(), meta)),
            KlujurVal::Set(s, _) => Some(KlujurVal::Set(s.clone(), meta)),
            KlujurVal::SortedMapBy(sm) => Some(KlujurVal::SortedMapBy(sm.with_meta(meta))),
            KlujurVal::SortedSetBy(ss) => Some(KlujurVal::SortedSetBy(ss.with_meta(meta))),
            _ => None,
        }
    }
}

/// Greatest common divisor using Euclidean algorithm
fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ============================================================================
// Display implementation
// ============================================================================

impl fmt::Display for KlujurVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Note: Metadata is not displayed (consistent with Clojure)
        match self {
            KlujurVal::Nil => write!(f, "nil"),
            KlujurVal::Bool(b) => write!(f, "{}", b),
            KlujurVal::Int(n) => write!(f, "{}", n),
            KlujurVal::Float(n) => {
                if n.is_nan() {
                    write!(f, "##NaN")
                } else if n.is_infinite() {
                    if *n > 0.0 {
                        write!(f, "##Inf")
                    } else {
                        write!(f, "##-Inf")
                    }
                } else if n.fract() == 0.0 {
                    write!(f, "{}.0", n)
                } else {
                    write!(f, "{}", n)
                }
            }
            KlujurVal::Ratio(num, den) => write!(f, "{}/{}", num, den),
            KlujurVal::Char(c) => write!(f, "\\{}", format_char(*c)),
            KlujurVal::String(s) => write!(f, "\"{}\"", escape_string(s)),
            KlujurVal::Symbol(sym, _) => write!(f, "{}", sym),
            KlujurVal::Keyword(kw) => write!(f, "{}", kw),
            KlujurVal::List(items, _) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            KlujurVal::Vector(items, _) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            KlujurVal::Map(map, _) => {
                write!(f, "{{")?;
                for (i, (k, v)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{} {}", k, v)?;
                }
                write!(f, "}}")
            }
            KlujurVal::Set(set, _) => {
                write!(f, "#{{")?;
                for (i, item) in set.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "}}")
            }
            KlujurVal::Fn(_) => write!(f, "#<fn>"),
            KlujurVal::NativeFn(nf) => write!(f, "#<native-fn {}>", nf.name),
            KlujurVal::Macro(_) => write!(f, "#<macro>"),
            KlujurVal::Var(v) => write!(f, "{}", v),
            KlujurVal::Atom(a) => write!(f, "{}", a),
            KlujurVal::Delay(d) => write!(f, "{}", d),
            KlujurVal::LazySeq(ls) => write!(f, "{}", ls),
            KlujurVal::Multimethod(mm) => write!(f, "{}", mm),
            KlujurVal::Hierarchy(h) => write!(f, "{}", h.borrow()),
            KlujurVal::Reduced(v) => write!(f, "#reduced[{}]", v),
            KlujurVal::Volatile(v) => write!(f, "{}", v),
            KlujurVal::Protocol(p) => write!(f, "{}", p),
            KlujurVal::Record(r) => write!(f, "{}", r),
            KlujurVal::SortedMapBy(sm) => write!(f, "{}", sm),
            KlujurVal::SortedSetBy(ss) => write!(f, "{}", ss),
            KlujurVal::Custom(c) => write!(f, "{}", c),
        }
    }
}

impl fmt::Debug for KlujurVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

fn format_char(c: char) -> String {
    match c {
        '\n' => "newline".to_string(),
        ' ' => "space".to_string(),
        '\t' => "tab".to_string(),
        '\r' => "return".to_string(),
        '\x08' => "backspace".to_string(),
        '\x0C' => "formfeed".to_string(),
        _ => c.to_string(),
    }
}

fn escape_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\n' => result.push_str("\\n"),
            '\t' => result.push_str("\\t"),
            '\r' => result.push_str("\\r"),
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            _ => result.push(c),
        }
    }
    result
}

// ============================================================================
// Equality and ordering (for use as map keys and set elements)
// ============================================================================

/// Normalize float bits for consistent hashing and equality.
/// - Treats +0.0 and -0.0 as the same value
/// - Treats all NaN bit patterns as the same value
fn normalize_float_bits(f: f64) -> u64 {
    if f.is_nan() {
        // All NaN values hash to the same canonical NaN bits
        f64::NAN.to_bits()
    } else if f == 0.0 {
        // +0.0 and -0.0 are equal, so they must hash the same
        0u64
    } else {
        f.to_bits()
    }
}

/// Hash a numeric value consistently across Int, Float, and Ratio types.
/// Equal values MUST hash identically to satisfy the Hash/Eq contract.
///
/// Strategy:
/// - Convert to float representation when the value can be exactly represented
/// - Use a "numeric" discriminant instead of per-type discriminants
fn hash_numeric<H: Hasher>(state: &mut H, int_val: Option<i64>, float_val: f64) {
    // Use a single discriminant for all numeric types
    const NUMERIC_DISCRIMINANT: u8 = 0;
    NUMERIC_DISCRIMINANT.hash(state);

    // If the float value is an exact integer that round-trips, use that for hashing
    // This ensures Int(n) and Float(n.0) hash the same when n.0 as i64 as f64 == n.0
    if let Some(n) = int_val {
        // Check if this int is exactly representable as f64
        if n as f64 as i64 == n {
            normalize_float_bits(n as f64).hash(state);
        } else {
            // Large integers that lose precision as f64 - hash as int
            // These can never equal a Float anyway
            n.hash(state);
        }
    } else {
        // For floats and ratios-as-floats, use normalised float bits
        normalize_float_bits(float_val).hash(state);
    }
}

impl PartialEq for KlujurVal {
    fn eq(&self, other: &Self) -> bool {
        // Note: Metadata is intentionally ignored in equality comparisons.
        // (= [1 2] (with-meta [1 2] {:a 1})) => true
        match (self, other) {
            (KlujurVal::Nil, KlujurVal::Nil) => true,
            (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a == b,
            (KlujurVal::Int(a), KlujurVal::Int(b)) => a == b,
            (KlujurVal::Float(a), KlujurVal::Float(b)) => {
                normalize_float_bits(*a) == normalize_float_bits(*b)
            }
            (KlujurVal::Int(a), KlujurVal::Float(b)) => {
                normalize_float_bits(*a as f64) == normalize_float_bits(*b)
            }
            (KlujurVal::Float(a), KlujurVal::Int(b)) => {
                normalize_float_bits(*a) == normalize_float_bits(*b as f64)
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::Ratio(bn, bd)) => an == bn && ad == bd,
            // Ratio-Int equality: a/b == c iff a == b*c (after normalisation, so gcd(a,b)=1)
            (KlujurVal::Ratio(num, den), KlujurVal::Int(n)) => *den == 1 && *num == *n,
            (KlujurVal::Int(n), KlujurVal::Ratio(num, den)) => *den == 1 && *num == *n,
            // Ratio-Float equality: convert ratio to float and compare
            (KlujurVal::Ratio(num, den), KlujurVal::Float(f)) => {
                normalize_float_bits(*num as f64 / *den as f64) == normalize_float_bits(*f)
            }
            (KlujurVal::Float(f), KlujurVal::Ratio(num, den)) => {
                normalize_float_bits(*f) == normalize_float_bits(*num as f64 / *den as f64)
            }
            (KlujurVal::Char(a), KlujurVal::Char(b)) => a == b,
            (KlujurVal::String(a), KlujurVal::String(b)) => a == b,
            (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a == b, // ignore metadata
            (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a == b,
            (KlujurVal::List(a, _), KlujurVal::List(b, _)) => a == b, // ignore metadata
            (KlujurVal::Vector(a, _), KlujurVal::Vector(b, _)) => a == b, // ignore metadata
            (KlujurVal::Map(a, _), KlujurVal::Map(b, _)) => a == b,   // ignore metadata
            (KlujurVal::Set(a, _), KlujurVal::Set(b, _)) => a == b,   // ignore metadata
            (KlujurVal::Fn(a), KlujurVal::Fn(b)) => a == b,
            (KlujurVal::NativeFn(a), KlujurVal::NativeFn(b)) => a == b,
            (KlujurVal::Macro(a), KlujurVal::Macro(b)) => a == b,
            (KlujurVal::Var(a), KlujurVal::Var(b)) => a == b,
            (KlujurVal::Atom(a), KlujurVal::Atom(b)) => a == b,
            (KlujurVal::Delay(a), KlujurVal::Delay(b)) => a == b,
            (KlujurVal::LazySeq(a), KlujurVal::LazySeq(b)) => a == b,
            (KlujurVal::Multimethod(a), KlujurVal::Multimethod(b)) => a == b,
            (KlujurVal::Hierarchy(a), KlujurVal::Hierarchy(b)) => Rc::ptr_eq(a, b),
            (KlujurVal::Reduced(a), KlujurVal::Reduced(b)) => a == b,
            (KlujurVal::Volatile(a), KlujurVal::Volatile(b)) => a == b,
            (KlujurVal::Protocol(a), KlujurVal::Protocol(b)) => a == b,
            (KlujurVal::Record(a), KlujurVal::Record(b)) => a == b,
            (KlujurVal::SortedMapBy(a), KlujurVal::SortedMapBy(b)) => a == b,
            (KlujurVal::SortedSetBy(a), KlujurVal::SortedSetBy(b)) => a == b,
            (KlujurVal::Custom(a), KlujurVal::Custom(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for KlujurVal {}

impl PartialOrd for KlujurVal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurVal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        // Type ordering for heterogeneous comparison
        // Note: Metadata is ignored in ordering (consistent with equality)
        fn type_order(v: &KlujurVal) -> u8 {
            match v {
                KlujurVal::Nil => 0,
                KlujurVal::Bool(_) => 1,
                KlujurVal::Int(_) => 2,
                KlujurVal::Float(_) => 2, // Same as Int for numeric comparison
                KlujurVal::Ratio(_, _) => 2,
                KlujurVal::Char(_) => 3,
                KlujurVal::String(_) => 4,
                KlujurVal::Symbol(_, _) => 5,
                KlujurVal::Keyword(_) => 6,
                KlujurVal::List(_, _) => 7,
                KlujurVal::Vector(_, _) => 8,
                KlujurVal::Map(_, _) => 9,
                KlujurVal::Set(_, _) => 10,
                KlujurVal::Fn(_) => 11,
                KlujurVal::NativeFn(_) => 12,
                KlujurVal::Macro(_) => 13,
                KlujurVal::Var(_) => 14,
                KlujurVal::Atom(_) => 15,
                KlujurVal::Delay(_) => 16,
                KlujurVal::LazySeq(_) => 17,
                KlujurVal::Multimethod(_) => 18,
                KlujurVal::Hierarchy(_) => 19,
                KlujurVal::Reduced(_) => 20,
                KlujurVal::Volatile(_) => 21,
                KlujurVal::Protocol(_) => 22,
                KlujurVal::Record(_) => 23,
                KlujurVal::SortedMapBy(_) => 24,
                KlujurVal::SortedSetBy(_) => 25,
                KlujurVal::Custom(_) => 26,
            }
        }

        let ta = type_order(self);
        let tb = type_order(other);

        if ta != tb {
            return ta.cmp(&tb);
        }

        match (self, other) {
            (KlujurVal::Nil, KlujurVal::Nil) => Ordering::Equal,
            (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a.cmp(b),
            (KlujurVal::Int(a), KlujurVal::Int(b)) => a.cmp(b),
            (KlujurVal::Float(a), KlujurVal::Float(b)) => {
                // Use normalized bits for total ordering (NaN sorts equal to itself)
                normalize_float_bits(*a).cmp(&normalize_float_bits(*b))
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::Ratio(bn, bd)) => {
                // Cross multiply to compare: an/ad vs bn/bd => an*bd vs bn*ad
                // Use i128 to avoid overflow
                ((*an as i128) * (*bd as i128)).cmp(&((*bn as i128) * (*ad as i128)))
            }
            (KlujurVal::Char(a), KlujurVal::Char(b)) => a.cmp(b),
            (KlujurVal::String(a), KlujurVal::String(b)) => a.cmp(b),
            (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a.cmp(b), // ignore metadata
            (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a.cmp(b),
            (KlujurVal::List(a, _), KlujurVal::List(b, _)) => a.cmp(b), // ignore metadata
            (KlujurVal::Vector(a, _), KlujurVal::Vector(b, _)) => a.cmp(b), // ignore metadata
            (KlujurVal::Map(a, _), KlujurVal::Map(b, _)) => {
                // Compare by entries (ignore metadata)
                a.iter().cmp(b.iter())
            }
            (KlujurVal::Set(a, _), KlujurVal::Set(b, _)) => a.iter().cmp(b.iter()), // ignore metadata
            (KlujurVal::Fn(a), KlujurVal::Fn(b)) => {
                // Use pointer comparison on the captured environment for consistent ordering
                // Cast fat pointer to thin pointer via *const () before converting to usize
                let a_ptr = Rc::as_ptr(&a.env) as *const () as usize;
                let b_ptr = Rc::as_ptr(&b.env) as *const () as usize;
                a_ptr.cmp(&b_ptr)
            }
            (KlujurVal::NativeFn(a), KlujurVal::NativeFn(b)) => a.name.cmp(&b.name),
            (KlujurVal::Macro(a), KlujurVal::Macro(b)) => {
                // Use pointer comparison on the captured environment for consistent ordering
                // Cast fat pointer to thin pointer via *const () before converting to usize
                let a_ptr = Rc::as_ptr(&a.env) as *const () as usize;
                let b_ptr = Rc::as_ptr(&b.env) as *const () as usize;
                a_ptr.cmp(&b_ptr)
            }
            (KlujurVal::Var(a), KlujurVal::Var(b)) => a.cmp(b),
            (KlujurVal::Atom(a), KlujurVal::Atom(b)) => a.cmp(b),
            (KlujurVal::Delay(a), KlujurVal::Delay(b)) => a.cmp(b),
            (KlujurVal::LazySeq(a), KlujurVal::LazySeq(b)) => a.cmp(b),
            (KlujurVal::Multimethod(a), KlujurVal::Multimethod(b)) => a.cmp(b),
            (KlujurVal::Hierarchy(a), KlujurVal::Hierarchy(b)) => {
                let a_ptr = Rc::as_ptr(a) as usize;
                let b_ptr = Rc::as_ptr(b) as usize;
                a_ptr.cmp(&b_ptr)
            }
            (KlujurVal::Reduced(a), KlujurVal::Reduced(b)) => a.cmp(b),
            (KlujurVal::Volatile(a), KlujurVal::Volatile(b)) => a.cmp(b),
            (KlujurVal::Protocol(a), KlujurVal::Protocol(b)) => a.cmp(b),
            (KlujurVal::Record(a), KlujurVal::Record(b)) => a.cmp(b),
            (KlujurVal::SortedMapBy(a), KlujurVal::SortedMapBy(b)) => a.cmp(b),
            (KlujurVal::SortedSetBy(a), KlujurVal::SortedSetBy(b)) => a.cmp(b),
            (KlujurVal::Custom(a), KlujurVal::Custom(b)) => a.cmp(b),
            _ => Ordering::Equal,
        }
    }
}

impl Hash for KlujurVal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Note: Metadata is intentionally ignored in hashing (consistent with equality)
        // Note: Numeric types (Int, Float, Ratio) use hash_numeric() instead of discriminant
        // hashing to ensure equal values hash identically (e.g., 1 == 1.0 must hash same)
        match self {
            KlujurVal::Nil => std::mem::discriminant(self).hash(state),
            KlujurVal::Bool(b) => {
                std::mem::discriminant(self).hash(state);
                b.hash(state);
            }
            // Numeric types: use consistent hashing across Int/Float/Ratio
            KlujurVal::Int(n) => hash_numeric(state, Some(*n), *n as f64),
            KlujurVal::Float(f) => hash_numeric(state, None, *f),
            KlujurVal::Ratio(num, den) => {
                // If den == 1, this equals an Int, so hash like the Int
                if *den == 1 {
                    hash_numeric(state, Some(*num), *num as f64);
                } else {
                    // Hash as the float representation for potential Float equality
                    hash_numeric(state, None, *num as f64 / *den as f64);
                }
            }
            KlujurVal::Char(c) => {
                std::mem::discriminant(self).hash(state);
                c.hash(state);
            }
            KlujurVal::String(s) => {
                std::mem::discriminant(self).hash(state);
                s.hash(state);
            }
            KlujurVal::Symbol(sym, _) => {
                std::mem::discriminant(self).hash(state);
                sym.hash(state); // ignore metadata
            }
            KlujurVal::Keyword(kw) => {
                std::mem::discriminant(self).hash(state);
                kw.hash(state);
            }
            KlujurVal::List(items, _) => {
                std::mem::discriminant(self).hash(state);
                items.hash(state); // ignore metadata
            }
            KlujurVal::Vector(items, _) => {
                std::mem::discriminant(self).hash(state);
                items.hash(state); // ignore metadata
            }
            KlujurVal::Map(map, _) => {
                std::mem::discriminant(self).hash(state);
                // ignore metadata
                for (k, v) in map.iter() {
                    k.hash(state);
                    v.hash(state);
                }
            }
            KlujurVal::Set(set, _) => {
                std::mem::discriminant(self).hash(state);
                // ignore metadata
                for item in set.iter() {
                    item.hash(state);
                }
            }
            KlujurVal::Fn(_) => {
                std::mem::discriminant(self).hash(state);
                // Functions don't have meaningful hash - use type discriminant only
            }
            KlujurVal::NativeFn(nf) => {
                std::mem::discriminant(self).hash(state);
                nf.name.hash(state);
            }
            KlujurVal::Macro(_) => {
                std::mem::discriminant(self).hash(state);
                // Macros don't have meaningful hash - use type discriminant only
            }
            KlujurVal::Var(v) => {
                std::mem::discriminant(self).hash(state);
                v.qualified_name().hash(state);
            }
            KlujurVal::Atom(a) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (atoms are identity-compared)
                (Rc::as_ptr(&a.value) as usize).hash(state);
            }
            KlujurVal::Delay(d) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (delays are identity-compared)
                (Rc::as_ptr(&d.state) as usize).hash(state);
            }
            KlujurVal::LazySeq(ls) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (lazy seqs are identity-compared)
                (Rc::as_ptr(ls.state()) as usize).hash(state);
            }
            KlujurVal::Multimethod(mm) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (multimethods are identity-compared)
                (Rc::as_ptr(&mm.methods) as usize).hash(state);
            }
            KlujurVal::Hierarchy(h) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (hierarchies are identity-compared)
                (Rc::as_ptr(h) as usize).hash(state);
            }
            KlujurVal::Reduced(v) => {
                std::mem::discriminant(self).hash(state);
                // Hash by inner value
                v.hash(state);
            }
            KlujurVal::Volatile(v) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (volatiles are identity-compared)
                (v.as_ptr() as usize).hash(state);
            }
            KlujurVal::Protocol(p) => {
                std::mem::discriminant(self).hash(state);
                // Hash by protocol name and namespace
                p.hash(state);
            }
            KlujurVal::Record(r) => {
                std::mem::discriminant(self).hash(state);
                // Hash by record type and values
                r.hash(state);
            }
            KlujurVal::SortedMapBy(sm) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (identity-based)
                sm.hash(state);
            }
            KlujurVal::SortedSetBy(ss) => {
                std::mem::discriminant(self).hash(state);
                // Hash by pointer address (identity-based)
                ss.hash(state);
            }
            KlujurVal::Custom(c) => {
                std::mem::discriminant(self).hash(state);
                c.hash(state);
            }
        }
    }
}

// ============================================================================
// From trait implementations
// ============================================================================

impl From<bool> for KlujurVal {
    fn from(b: bool) -> Self {
        KlujurVal::Bool(b)
    }
}

impl From<i64> for KlujurVal {
    fn from(n: i64) -> Self {
        KlujurVal::int(n)
    }
}

impl From<i32> for KlujurVal {
    fn from(n: i32) -> Self {
        KlujurVal::int(n as i64)
    }
}

impl From<usize> for KlujurVal {
    fn from(n: usize) -> Self {
        KlujurVal::int(n as i64)
    }
}

impl From<f64> for KlujurVal {
    fn from(n: f64) -> Self {
        KlujurVal::float(n)
    }
}

impl From<f32> for KlujurVal {
    fn from(n: f32) -> Self {
        KlujurVal::float(n as f64)
    }
}

impl From<char> for KlujurVal {
    fn from(c: char) -> Self {
        KlujurVal::char(c)
    }
}

impl From<String> for KlujurVal {
    fn from(s: String) -> Self {
        KlujurVal::string(s)
    }
}

impl From<&str> for KlujurVal {
    fn from(s: &str) -> Self {
        KlujurVal::string(s)
    }
}

impl<T: Into<KlujurVal>> From<Vec<T>> for KlujurVal {
    fn from(v: Vec<T>) -> Self {
        KlujurVal::vector(v.into_iter().map(Into::into).collect())
    }
}

impl<T: Into<KlujurVal>> From<Option<T>> for KlujurVal {
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(v) => v.into(),
            None => KlujurVal::Nil,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nil() {
        let val = KlujurVal::nil();
        assert!(val.is_nil());
        assert!(!val.is_truthy());
        assert_eq!(format!("{}", val), "nil");
    }

    #[test]
    fn test_bool() {
        let t = KlujurVal::bool(true);
        let f = KlujurVal::bool(false);

        assert!(t.is_truthy());
        assert!(!f.is_truthy());
        assert_eq!(format!("{}", t), "true");
        assert_eq!(format!("{}", f), "false");
    }

    #[test]
    fn test_int() {
        let val = KlujurVal::int(42);
        assert!(val.is_truthy());
        assert_eq!(format!("{}", val), "42");
    }

    #[test]
    fn test_float() {
        let val = KlujurVal::float(3.14);
        assert_eq!(format!("{}", val), "3.14");

        let whole = KlujurVal::float(42.0);
        assert_eq!(format!("{}", whole), "42.0");

        let inf = KlujurVal::float(f64::INFINITY);
        assert_eq!(format!("{}", inf), "##Inf");

        let neg_inf = KlujurVal::float(f64::NEG_INFINITY);
        assert_eq!(format!("{}", neg_inf), "##-Inf");

        let nan = KlujurVal::float(f64::NAN);
        assert_eq!(format!("{}", nan), "##NaN");
    }

    #[test]
    fn test_ratio() {
        // Ratio reduces automatically
        let val = KlujurVal::ratio(2, 4);
        assert_eq!(format!("{}", val), "1/2");

        // Ratio becomes int when denominator is 1
        let whole = KlujurVal::ratio(4, 2);
        assert!(matches!(whole, KlujurVal::Int(2)));
    }

    #[test]
    fn test_string() {
        let val = KlujurVal::string("hello");
        assert_eq!(format!("{}", val), "\"hello\"");

        let escaped = KlujurVal::string("hello\nworld");
        assert_eq!(format!("{}", escaped), "\"hello\\nworld\"");
    }

    #[test]
    fn test_char() {
        let val = KlujurVal::char('a');
        assert_eq!(format!("{}", val), "\\a");

        let newline = KlujurVal::char('\n');
        assert_eq!(format!("{}", newline), "\\newline");

        let space = KlujurVal::char(' ');
        assert_eq!(format!("{}", space), "\\space");
    }

    #[test]
    fn test_vector() {
        let val = KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
        ]);
        assert_eq!(format!("{}", val), "[1 2 3]");
    }

    #[test]
    fn test_list() {
        let val = KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
        ]);
        assert_eq!(format!("{}", val), "(1 2 3)");
    }

    #[test]
    fn test_equality() {
        assert_eq!(KlujurVal::int(42), KlujurVal::int(42));
        assert_ne!(KlujurVal::int(42), KlujurVal::int(43));
        assert_eq!(KlujurVal::nil(), KlujurVal::nil());
        assert_ne!(KlujurVal::nil(), KlujurVal::bool(false));
    }

    #[test]
    fn test_type_name() {
        assert_eq!(KlujurVal::nil().type_name(), "nil");
        assert_eq!(KlujurVal::bool(true).type_name(), "bool");
        assert_eq!(KlujurVal::int(42).type_name(), "int");
        assert_eq!(KlujurVal::float(3.14).type_name(), "float");
    }
}
