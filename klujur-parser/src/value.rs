// klujur-parser - Value types for Klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Core value type for Klujur.
//!
//! `KlujurVal` is the central enum representing all Klujur values.

// KlujurVal contains interior-mutable types (Var, Atom, Delay, Volatile) but hashes
// by identity/qualified-name, not mutable contents. This is intentional and safe.
#![allow(clippy::mutable_key_type)]

use std::any::Any;
use std::cell::Cell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use im::{OrdMap, OrdSet, Vector};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

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
    #[inline]
    #[must_use]
    pub fn type_name(&self) -> &'static str {
        self.inner.type_name()
    }

    /// Attempt to downcast to a specific type.
    #[inline]
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
    BigInt,
    Float,
    Ratio,
    BigRatio,
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
    /// Chunk of realized values
    Chunk,
    /// Buffer for building chunks
    ChunkBuffer,
    /// Chunked lazy sequence
    ChunkedSeq,
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
    #[inline]
    #[must_use]
    pub fn get_impl(&self, type_key: &TypeKey) -> Option<TypeImpl> {
        self.impls.borrow().get(type_key).cloned()
    }

    /// Check if a type has an implementation for this protocol
    #[inline]
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

    #[inline]
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
    /// All values: base fields + any extra keys added via assoc.
    /// Uses OrdMap for efficient iteration in sorted order (O(n) hash instead of O(n log n)).
    pub values: OrdMap<Keyword, KlujurVal>,
}

impl RecordInstance {
    /// Create a new record instance.
    pub fn new(
        record_type: Symbol,
        record_ns: String,
        fields: Vec<Symbol>,
        values: OrdMap<Keyword, KlujurVal>,
    ) -> Self {
        RecordInstance {
            record_type,
            record_ns,
            fields,
            values,
        }
    }

    /// Get a field value by keyword.
    #[inline]
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
    #[inline]
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
        // OrdMap maintains sorted order, so iteration is O(n) not O(n log n)
        for (k, v) in &self.values {
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
    #[inline]
    #[must_use]
    pub fn comparator(&self) -> &KlujurVal {
        &self.comparator
    }

    /// Get a clone of the comparator Rc.
    #[inline]
    #[must_use]
    pub fn comparator_rc(&self) -> Rc<KlujurVal> {
        Rc::clone(&self.comparator)
    }

    /// Get the number of entries.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.borrow().len()
    }

    /// Check if the map is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.borrow().is_empty()
    }

    /// Get a clone of all entries (use `try_borrow_entries()` for read-only access without cloning).
    ///
    /// # Errors
    ///
    /// Returns an error if the entries are currently borrowed mutably,
    /// which could occur during re-entrant comparator access.
    #[inline]
    pub fn entries(&self) -> Result<Vec<(KlujurVal, KlujurVal)>, &'static str> {
        self.entries
            .try_borrow()
            .map(|e| e.clone())
            .map_err(|_| "Re-entrant access to SortedMapBy during comparator call")
    }

    /// Borrow the entries without cloning (preferred for iteration).
    ///
    /// # Errors
    ///
    /// Returns an error if the entries are currently borrowed mutably.
    #[inline]
    pub fn try_borrow_entries(
        &self,
    ) -> Result<std::cell::Ref<'_, Vec<(KlujurVal, KlujurVal)>>, &'static str> {
        self.entries
            .try_borrow()
            .map_err(|_| "Re-entrant access to SortedMapBy during comparator call")
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
    #[inline]
    #[must_use]
    pub fn comparator(&self) -> &KlujurVal {
        &self.comparator
    }

    /// Get a clone of the comparator Rc.
    #[inline]
    #[must_use]
    pub fn comparator_rc(&self) -> Rc<KlujurVal> {
        Rc::clone(&self.comparator)
    }

    /// Get the number of elements.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.elements.borrow().len()
    }

    /// Check if the set is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.elements.borrow().is_empty()
    }

    /// Get a clone of all elements.
    ///
    /// # Errors
    ///
    /// Returns an error if the elements are currently borrowed mutably,
    /// which could occur during re-entrant comparator access.
    #[inline]
    pub fn elements(&self) -> Result<Vec<KlujurVal>, &'static str> {
        self.elements
            .try_borrow()
            .map(|e| e.clone())
            .map_err(|_| "Re-entrant access to SortedSetBy during comparator call")
    }

    /// Borrow the elements without cloning (preferred for iteration).
    #[inline]
    pub fn try_borrow_elements(&self) -> Result<std::cell::Ref<'_, Vec<KlujurVal>>, &'static str> {
        self.elements
            .try_borrow()
            .map_err(|_| "Re-entrant access to SortedSetBy during comparator call")
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
///
/// ## Size and Boxing Decision
///
/// **DECISION: No boxing of large variants**
///
/// **SIZE ANALYSIS (as of 2025):**
/// - Total enum size: 80 bytes (10 machine words)
/// - Largest variant: List/Vector with `Vector<KlujurVal>` (64 bytes) + `Option<Rc<Meta>>` (8 bytes)
/// - Component sizes:
///   - `Vector<KlujurVal>`: 64 bytes (im crate, uses Rc internally for structural sharing)
///   - `OrdMap<KlujurVal, KlujurVal>`: 16 bytes (just an Rc pointer)
///   - `BigInt`: 32 bytes
///   - `Option<Rc<Meta>>`: 8 bytes
///
/// **RATIONALE:**
/// 1. 80 bytes is reasonable for an enum representing all language values
/// 2. The `im` crate's persistent data structures already use Rc internally
/// 3. Boxing would add an extra heap allocation and pointer indirection
/// 4. This would hurt performance for the most common operations (list/vector access)
/// 5. Memory layout is already optimised by the im crate's design
///
/// **MEASUREMENT:** See `size_tests::test_klujur_val_size` in this file
#[derive(Clone)]
pub enum KlujurVal {
    /// The nil value, representing nothing/absence
    Nil,
    /// Boolean true or false
    Bool(bool),
    /// 64-bit signed integer
    Int(i64),
    /// Arbitrary precision integer
    BigInt(BigInt),
    /// 64-bit floating point number
    Float(f64),
    /// Rational number (numerator/denominator)
    Ratio(i64, i64),
    /// Arbitrary precision rational number (numerator/denominator)
    BigRatio(BigInt, BigInt),
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
    /// Chunk of realized values (for chunked sequences)
    Chunk(KlujurChunk),
    /// Buffer for building chunks incrementally
    ChunkBuffer(KlujurChunkBuffer),
    /// Chunked lazy sequence (efficient batch processing)
    ChunkedSeq(KlujurChunkedSeq),
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
    /// Preconditions (:pre) - list of expressions that must all be truthy
    pub pre: Vec<KlujurVal>,
    /// Postconditions (:post) - list of expressions (can use % for return value)
    pub post: Vec<KlujurVal>,
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
            pre: Vec::new(),
            post: Vec::new(),
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
            pre: Vec::new(),
            post: Vec::new(),
            body,
        }
    }

    /// Create a new arity definition with pre/post conditions.
    pub fn with_conditions(
        params: Vec<Symbol>,
        rest_param: Option<Symbol>,
        param_patterns: Vec<KlujurVal>,
        rest_pattern: Option<KlujurVal>,
        pre: Vec<KlujurVal>,
        post: Vec<KlujurVal>,
        body: Vec<KlujurVal>,
    ) -> Self {
        FnArity {
            params,
            rest_param,
            param_patterns,
            rest_pattern,
            pre,
            post,
            body,
        }
    }

    /// Get the minimum number of arguments this arity accepts.
    #[inline]
    #[must_use]
    pub fn min_arity(&self) -> usize {
        self.params.len()
    }

    /// Check if this arity can accept the given number of arguments.
    #[inline]
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
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn params(&self) -> Option<&[Symbol]> {
        self.arities.first().map(|a| a.params.as_slice())
    }

    /// Get rest parameter of the first (or only) arity.
    ///
    /// Returns `None` if the function has no arities.
    #[inline]
    #[must_use]
    pub fn rest_param(&self) -> Option<&Symbol> {
        self.arities.first().and_then(|a| a.rest_param.as_ref())
    }

    /// Get body of the first (or only) arity.
    ///
    /// Returns `None` if the function has no arities.
    #[inline]
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
/// - A bound flag (whether the var has a root binding)
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
    /// Whether this var has a root binding (false for declared/unbound vars)
    bound: Rc<RefCell<bool>>,
    /// Var metadata (mutable, for doc strings, arglists, etc.)
    meta: Rc<RefCell<Option<Meta>>>,
}

impl KlujurVar {
    /// Create a new Var with a value (bound).
    pub fn new(name: String, value: KlujurVal) -> Self {
        KlujurVar {
            ns: None,
            name,
            root: Rc::new(RefCell::new(value)),
            dynamic: Rc::new(RefCell::new(false)),
            bound: Rc::new(RefCell::new(true)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Create a new unbound Var (for declare).
    pub fn new_unbound(name: String) -> Self {
        KlujurVar {
            ns: None,
            name,
            root: Rc::new(RefCell::new(KlujurVal::Nil)),
            dynamic: Rc::new(RefCell::new(false)),
            bound: Rc::new(RefCell::new(false)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Create a new Var with namespace (bound).
    pub fn new_with_ns(ns: String, name: String, value: KlujurVal) -> Self {
        KlujurVar {
            ns: Some(ns),
            name,
            root: Rc::new(RefCell::new(value)),
            dynamic: Rc::new(RefCell::new(false)),
            bound: Rc::new(RefCell::new(true)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Create a new unbound Var with namespace (for declare).
    pub fn new_unbound_with_ns(ns: String, name: String) -> Self {
        KlujurVar {
            ns: Some(ns),
            name,
            root: Rc::new(RefCell::new(KlujurVal::Nil)),
            dynamic: Rc::new(RefCell::new(false)),
            bound: Rc::new(RefCell::new(false)),
            meta: Rc::new(RefCell::new(None)),
        }
    }

    /// Get the current value (deref).
    /// Note: Thread-local bindings are checked in klujur-core, not here,
    /// to avoid circular dependency. This only returns the root value.
    #[inline]
    #[must_use]
    pub fn deref(&self) -> KlujurVal {
        self.root.borrow().clone()
    }

    /// Set the root value.
    pub fn set_root(&self, value: KlujurVal) {
        *self.root.borrow_mut() = value;
    }

    /// Check if this var is dynamic.
    #[inline]
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

    /// Check if this var has a root binding.
    #[inline]
    #[must_use]
    pub fn is_bound(&self) -> bool {
        *self.bound.borrow()
    }

    /// Set the bound flag and root value (used when binding an unbound var).
    pub fn bind(&self, value: KlujurVal) {
        *self.root.borrow_mut() = value;
        *self.bound.borrow_mut() = true;
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn is_realized(&self) -> bool {
        matches!(*self.state.borrow(), DelayState::Realized(_))
    }

    /// Get the thunk if pending, or None if already realized.
    #[inline]
    #[must_use]
    pub fn get_thunk(&self) -> Option<KlujurVal> {
        match &*self.state.borrow() {
            DelayState::Pending(thunk) => Some(thunk.clone()),
            DelayState::Realized(_) => None,
        }
    }

    /// Get the cached value if realized, or None if pending.
    #[inline]
    #[must_use]
    pub fn get_cached(&self) -> Option<KlujurVal> {
        match &*self.state.borrow() {
            DelayState::Pending(_) => None,
            DelayState::Realized(val) => Some(val.clone()),
        }
    }

    /// Set the realized value (called after evaluating the thunk).
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn is_realized(&self) -> bool {
        matches!(*self.state.borrow(), LazySeqState::Realized(_))
    }

    /// Get the thunk if pending, or None if already realized.
    #[inline]
    #[must_use]
    pub fn get_thunk(&self) -> Option<KlujurFn> {
        match &*self.state.borrow() {
            LazySeqState::Pending(thunk) => Some(thunk.clone()),
            LazySeqState::Realized(_) => None,
        }
    }

    /// Get the cached result if realized, or None if pending.
    #[inline]
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
// Chunked Sequence Types
// ============================================================================

/// A chunk of realized values (typically 32 elements).
/// Used for efficient batch processing of lazy sequences.
#[derive(Clone)]
pub struct KlujurChunk {
    /// The realized elements
    elements: Rc<Vec<KlujurVal>>,
    /// Starting offset (for efficient slicing without copying)
    offset: usize,
}

impl KlujurChunk {
    /// Default chunk size (matches Clojure)
    pub const CHUNK_SIZE: usize = 32;

    /// Create a new chunk from a vector of values.
    #[must_use]
    pub fn new(elements: Vec<KlujurVal>) -> Self {
        KlujurChunk {
            elements: Rc::new(elements),
            offset: 0,
        }
    }

    /// Create an empty chunk.
    #[must_use]
    pub fn empty() -> Self {
        KlujurChunk {
            elements: Rc::new(Vec::new()),
            offset: 0,
        }
    }

    /// Number of elements in this chunk (accounting for offset).
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.elements.len().saturating_sub(self.offset)
    }

    /// Check if the chunk is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the first element, if any.
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<&KlujurVal> {
        self.elements.get(self.offset)
    }

    /// Get the nth element (0-indexed from current offset).
    #[inline]
    #[must_use]
    pub fn nth(&self, n: usize) -> Option<&KlujurVal> {
        self.elements.get(self.offset + n)
    }

    /// Create a new chunk with the first element dropped.
    /// Returns None if only one element remains.
    #[must_use]
    pub fn drop_first(&self) -> Option<KlujurChunk> {
        if self.offset + 1 < self.elements.len() {
            Some(KlujurChunk {
                elements: Rc::clone(&self.elements),
                offset: self.offset + 1,
            })
        } else {
            None
        }
    }

    /// Iterate over elements in this chunk.
    pub fn iter(&self) -> impl Iterator<Item = &KlujurVal> {
        self.elements[self.offset..].iter()
    }

    /// Convert to a vector of values.
    #[must_use]
    pub fn to_vec(&self) -> Vec<KlujurVal> {
        self.elements[self.offset..].to_vec()
    }
}

impl fmt::Debug for KlujurChunk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Chunk: {} elements>", self.len())
    }
}

impl fmt::Display for KlujurChunk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, val) in self.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", val)?;
        }
        write!(f, "]")
    }
}

impl PartialEq for KlujurChunk {
    fn eq(&self, other: &Self) -> bool {
        // Compare by content
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl Eq for KlujurChunk {}

impl PartialOrd for KlujurChunk {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurChunk {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.cmp(b) {
                std::cmp::Ordering::Equal => continue,
                ord => return ord,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl std::hash::Hash for KlujurChunk {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for val in self.iter() {
            val.hash(state);
        }
    }
}

/// A buffer for building chunks incrementally.
/// Used by map/filter to collect transformed elements.
#[derive(Clone)]
pub struct KlujurChunkBuffer {
    /// The accumulated elements
    buffer: Rc<RefCell<Vec<KlujurVal>>>,
}

impl KlujurChunkBuffer {
    /// Create a new chunk buffer with the given capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        KlujurChunkBuffer {
            buffer: Rc::new(RefCell::new(Vec::with_capacity(capacity))),
        }
    }

    /// Append a value to the buffer.
    pub fn add(&self, val: KlujurVal) {
        self.buffer.borrow_mut().push(val);
    }

    /// Finalize the buffer into a chunk, consuming the contents.
    #[must_use]
    pub fn to_chunk(&self) -> KlujurChunk {
        let elements = std::mem::take(&mut *self.buffer.borrow_mut());
        KlujurChunk::new(elements)
    }

    /// Get the current count of elements.
    #[must_use]
    pub fn count(&self) -> usize {
        self.buffer.borrow().len()
    }
}

impl fmt::Debug for KlujurChunkBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<ChunkBuffer: {} elements>", self.count())
    }
}

impl fmt::Display for KlujurChunkBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<ChunkBuffer: {} elements>", self.count())
    }
}

impl PartialEq for KlujurChunkBuffer {
    fn eq(&self, other: &Self) -> bool {
        // Buffers are equal if they point to the same underlying storage
        Rc::ptr_eq(&self.buffer, &other.buffer)
    }
}

impl Eq for KlujurChunkBuffer {}

impl PartialOrd for KlujurChunkBuffer {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurChunkBuffer {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let self_ptr = Rc::as_ptr(&self.buffer) as usize;
        let other_ptr = Rc::as_ptr(&other.buffer) as usize;
        self_ptr.cmp(&other_ptr)
    }
}

impl std::hash::Hash for KlujurChunkBuffer {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.buffer) as usize).hash(state);
    }
}

/// A native thunk for chunked sequences.
/// Can be either a general-purpose closure or a specialized range iterator.
#[derive(Clone)]
pub enum NativeChunkThunk {
    /// General-purpose closure thunk - takes no arguments, returns ChunkedSeq or Nil.
    Closure(Rc<dyn Fn() -> std::result::Result<KlujurVal, String>>),
    /// Optimized range iterator - stores range parameters, no closures needed.
    Range { start: i64, end: i64, step: i64 },
}

/// Internal state of a chunked sequence's rest thunk.
#[derive(Clone)]
pub enum ChunkedRestState {
    /// Not yet evaluated - contains a zero-arg Klujur function to call
    Pending(KlujurFn),
    /// Not yet evaluated - contains a native (Rust) thunk
    PendingNative(NativeChunkThunk),
    /// Already evaluated - contains the rest as a seqable value (or Nil if exhausted).
    /// The rest can be any seqable type (ChunkedSeq, LazySeq, List, Vector, etc.)
    Realized(Box<KlujurVal>),
}

/// A chunked lazy sequence - processes elements in batches for efficiency.
#[derive(Clone)]
pub struct KlujurChunkedSeq {
    /// Current chunk of realized elements
    chunk: KlujurChunk,
    /// Lazy thunk for the rest of the sequence
    rest: Rc<RefCell<ChunkedRestState>>,
}

impl KlujurChunkedSeq {
    /// Create a new chunked sequence from a chunk and a rest thunk (Klujur function).
    #[must_use]
    pub fn new(chunk: KlujurChunk, rest_thunk: KlujurFn) -> Self {
        KlujurChunkedSeq {
            chunk,
            rest: Rc::new(RefCell::new(ChunkedRestState::Pending(rest_thunk))),
        }
    }

    /// Create a new chunked sequence from a chunk and a native (Rust) thunk.
    #[must_use]
    pub fn new_native(chunk: KlujurChunk, rest_thunk: NativeChunkThunk) -> Self {
        KlujurChunkedSeq {
            chunk,
            rest: Rc::new(RefCell::new(ChunkedRestState::PendingNative(rest_thunk))),
        }
    }

    /// Create a chunked sequence with an already-realized rest.
    /// The rest should be a seqable value (ChunkedSeq, LazySeq, List, etc.) or Nil.
    #[must_use]
    pub fn with_rest(chunk: KlujurChunk, rest: KlujurVal) -> Self {
        KlujurChunkedSeq {
            chunk,
            rest: Rc::new(RefCell::new(ChunkedRestState::Realized(Box::new(rest)))),
        }
    }

    /// Get a reference to the current chunk.
    #[inline]
    #[must_use]
    pub fn chunk(&self) -> &KlujurChunk {
        &self.chunk
    }

    /// Get a reference to the rest state.
    #[inline]
    #[must_use]
    pub fn rest_state(&self) -> &Rc<RefCell<ChunkedRestState>> {
        &self.rest
    }

    /// Check if the rest has been realized.
    #[inline]
    #[must_use]
    pub fn is_rest_realized(&self) -> bool {
        matches!(*self.rest.borrow(), ChunkedRestState::Realized(_))
    }

    /// Get the rest thunk if pending (Klujur function), or None otherwise.
    #[must_use]
    pub fn get_rest_thunk(&self) -> Option<KlujurFn> {
        match &*self.rest.borrow() {
            ChunkedRestState::Pending(thunk) => Some(thunk.clone()),
            ChunkedRestState::PendingNative(_) | ChunkedRestState::Realized(_) => None,
        }
    }

    /// Get the native rest thunk if pending, or None otherwise.
    #[must_use]
    pub fn get_native_rest_thunk(&self) -> Option<NativeChunkThunk> {
        match &*self.rest.borrow() {
            ChunkedRestState::PendingNative(thunk) => Some(thunk.clone()),
            ChunkedRestState::Pending(_) | ChunkedRestState::Realized(_) => None,
        }
    }

    /// Get the cached rest if realized, or None if still pending.
    #[must_use]
    pub fn get_cached_rest(&self) -> Option<KlujurVal> {
        match &*self.rest.borrow() {
            ChunkedRestState::Pending(_) | ChunkedRestState::PendingNative(_) => None,
            ChunkedRestState::Realized(rest) => Some((**rest).clone()),
        }
    }

    /// Set the realized rest (called after evaluating the thunk).
    /// The rest should be a seqable value (ChunkedSeq, LazySeq, etc.) or Nil.
    pub fn set_rest_realized(&self, rest: KlujurVal) {
        *self.rest.borrow_mut() = ChunkedRestState::Realized(Box::new(rest));
    }

    /// Create a new chunked seq with the first element dropped from the chunk.
    /// If the chunk is exhausted, returns None (caller should force rest).
    #[must_use]
    pub fn drop_first(&self) -> Option<KlujurChunkedSeq> {
        self.chunk.drop_first().map(|new_chunk| KlujurChunkedSeq {
            chunk: new_chunk,
            rest: Rc::clone(&self.rest),
        })
    }
}

impl fmt::Debug for KlujurChunkedSeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<ChunkedSeq: chunk={}>", self.chunk.len())
    }
}

impl fmt::Display for KlujurChunkedSeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Display the current chunk, with "..." for unforced rest
        write!(f, "(")?;
        for (i, val) in self.chunk.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", val)?;
        }
        match &*self.rest.borrow() {
            ChunkedRestState::Pending(_) | ChunkedRestState::PendingNative(_) => write!(f, " ...")?,
            ChunkedRestState::Realized(rest) => {
                if **rest != KlujurVal::Nil {
                    write!(f, " ...")?;
                }
            }
        }
        write!(f, ")")
    }
}

impl PartialEq for KlujurChunkedSeq {
    fn eq(&self, other: &Self) -> bool {
        // ChunkedSeqs are equal if they point to the same rest state
        // (similar to LazySeq semantics)
        Rc::ptr_eq(&self.rest, &other.rest) && self.chunk == other.chunk
    }
}

impl Eq for KlujurChunkedSeq {}

impl PartialOrd for KlujurChunkedSeq {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KlujurChunkedSeq {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by pointer address for consistent ordering
        let self_ptr = Rc::as_ptr(&self.rest) as usize;
        let other_ptr = Rc::as_ptr(&other.rest) as usize;
        match self_ptr.cmp(&other_ptr) {
            std::cmp::Ordering::Equal => self.chunk.cmp(&other.chunk),
            ord => ord,
        }
    }
}

impl std::hash::Hash for KlujurChunkedSeq {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.rest) as usize).hash(state);
        self.chunk.hash(state);
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
    #[inline]
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
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn nil() -> Self {
        KlujurVal::Nil
    }

    /// Create a boolean value
    #[inline]
    #[must_use]
    pub fn bool(b: bool) -> Self {
        KlujurVal::Bool(b)
    }

    /// Create an integer value
    #[inline]
    #[must_use]
    pub fn int(n: i64) -> Self {
        KlujurVal::Int(n)
    }

    /// Create an arbitrary precision integer value, normalising to Int if it fits.
    /// Use this for auto-promoted values (overflow results).
    #[inline]
    #[must_use]
    pub fn bigint(n: BigInt) -> Self {
        // If it fits in i64, use Int for efficiency
        if let Some(i) = n.to_i64() {
            KlujurVal::Int(i)
        } else {
            KlujurVal::BigInt(n)
        }
    }

    /// Create an arbitrary precision integer value without normalising.
    /// Use this for explicit BigInt literals (with N suffix) to preserve the type.
    #[inline]
    #[must_use]
    pub fn bigint_literal(n: BigInt) -> Self {
        KlujurVal::BigInt(n)
    }

    /// Create a float value
    #[inline]
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

    /// Create an arbitrary precision ratio value, reducing to lowest terms.
    /// Returns `None` if denominator is zero.
    #[must_use]
    pub fn try_bigratio(num: BigInt, den: BigInt) -> Option<Self> {
        use num_bigint::Sign;
        use num_traits::{One, Zero};

        if den.is_zero() {
            return None;
        }

        // Calculate GCD for reduction
        fn bigint_gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
            while !b.is_zero() {
                let t = b.clone();
                b = &a % &b;
                a = t;
            }
            a
        }

        let g = bigint_gcd(num.clone().abs(), den.clone().abs());
        let (num, den) = if den.sign() == Sign::Minus {
            (-&num / &g, -&den / &g)
        } else {
            (&num / &g, &den / &g)
        };

        if den.is_one() {
            // Just an integer
            Some(Self::bigint(num))
        } else if let (Some(n), Some(d)) = (num.to_i64(), den.to_i64()) {
            // Fits in regular ratio
            Some(KlujurVal::Ratio(n, d))
        } else {
            Some(KlujurVal::BigRatio(num, den))
        }
    }

    /// Create an arbitrary precision ratio value, reducing to lowest terms.
    /// Panics if denominator is zero.
    #[must_use]
    pub fn bigratio(num: BigInt, den: BigInt) -> Self {
        Self::try_bigratio(num, den).expect("Division by zero in bigratio")
    }

    /// Create a character value
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn is_nil(&self) -> bool {
        matches!(self, KlujurVal::Nil)
    }

    /// Check if this value is truthy (not nil and not false)
    #[inline]
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        !matches!(self, KlujurVal::Nil | KlujurVal::Bool(false))
    }

    /// Get the type name as a string
    #[inline]
    #[must_use]
    pub fn type_name(&self) -> &'static str {
        match self {
            KlujurVal::Nil => "nil",
            KlujurVal::Bool(_) => "bool",
            KlujurVal::Int(_) => "int",
            KlujurVal::BigInt(_) => "bigint",
            KlujurVal::Float(_) => "float",
            KlujurVal::Ratio(_, _) => "ratio",
            KlujurVal::BigRatio(_, _) => "ratio",
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
            KlujurVal::Chunk(_) => "chunk",
            KlujurVal::ChunkBuffer(_) => "chunk-buffer",
            KlujurVal::ChunkedSeq(_) => "chunked-seq",
        }
    }

    /// Get the type key for protocol dispatch.
    ///
    /// This returns a TypeKey that can be used to look up protocol
    /// implementations for this value's type.
    #[inline]
    #[must_use]
    pub fn type_key(&self) -> TypeKey {
        match self {
            KlujurVal::Nil => TypeKey::Nil,
            KlujurVal::Bool(_) => TypeKey::Bool,
            KlujurVal::Int(_) => TypeKey::Int,
            KlujurVal::BigInt(_) => TypeKey::BigInt,
            KlujurVal::Float(_) => TypeKey::Float,
            KlujurVal::Ratio(_, _) => TypeKey::Ratio,
            KlujurVal::BigRatio(_, _) => TypeKey::BigRatio,
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
            KlujurVal::Chunk(_) => TypeKey::Chunk,
            KlujurVal::ChunkBuffer(_) => TypeKey::ChunkBuffer,
            KlujurVal::ChunkedSeq(_) => TypeKey::ChunkedSeq,
        }
    }

    /// Create an atom value
    #[inline]
    pub fn atom(value: KlujurVal) -> Self {
        KlujurVal::Atom(KlujurAtom::new(value))
    }

    /// Create a delay value with a thunk
    #[inline]
    pub fn delay(thunk: KlujurVal) -> Self {
        KlujurVal::Delay(KlujurDelay::new(thunk))
    }

    /// Create a lazy sequence value with a thunk
    #[inline]
    pub fn lazy_seq(thunk: KlujurFn) -> Self {
        KlujurVal::LazySeq(KlujurLazySeq::new(thunk))
    }

    /// Create a new hierarchy value
    #[inline]
    pub fn hierarchy() -> Self {
        KlujurVal::Hierarchy(Rc::new(RefCell::new(KlujurHierarchy::new())))
    }

    /// Create a hierarchy value from an existing hierarchy
    #[inline]
    pub fn from_hierarchy(h: Rc<RefCell<KlujurHierarchy>>) -> Self {
        KlujurVal::Hierarchy(h)
    }

    /// Create a reduced value (for transducer early termination)
    #[inline]
    pub fn reduced(value: KlujurVal) -> Self {
        KlujurVal::Reduced(Box::new(value))
    }

    /// Create a volatile reference
    #[inline]
    pub fn volatile(value: KlujurVal) -> Self {
        KlujurVal::Volatile(KlujurVolatile::new(value))
    }

    /// Create a protocol value
    #[inline]
    pub fn protocol(protocol: Protocol) -> Self {
        KlujurVal::Protocol(KlujurProtocol::new(protocol))
    }

    /// Create a protocol value from an existing Rc<Protocol>
    #[inline]
    pub fn from_protocol(protocol: Rc<Protocol>) -> Self {
        KlujurVal::Protocol(KlujurProtocol(protocol))
    }

    /// Create a record value from a RecordInstance
    #[inline]
    pub fn record(instance: RecordInstance) -> Self {
        KlujurVal::Record(Rc::new(instance))
    }

    /// Create a record value from an existing Rc<RecordInstance>
    #[inline]
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

    /// Create a chunk value from a vector of values.
    #[inline]
    pub fn chunk(elements: Vec<KlujurVal>) -> Self {
        KlujurVal::Chunk(KlujurChunk::new(elements))
    }

    /// Create a chunk buffer with the given capacity.
    #[inline]
    pub fn chunk_buffer(capacity: usize) -> Self {
        KlujurVal::ChunkBuffer(KlujurChunkBuffer::new(capacity))
    }

    /// Create a chunked sequence from a chunk and rest thunk.
    #[inline]
    pub fn chunked_seq(chunk: KlujurChunk, rest_thunk: KlujurFn) -> Self {
        KlujurVal::ChunkedSeq(KlujurChunkedSeq::new(chunk, rest_thunk))
    }

    /// Create a chunked sequence with an already-realized rest.
    /// The rest should be a seqable value (ChunkedSeq, LazySeq, etc.) or Nil.
    #[inline]
    pub fn chunked_seq_with_rest(chunk: KlujurChunk, rest: KlujurVal) -> Self {
        KlujurVal::ChunkedSeq(KlujurChunkedSeq::with_rest(chunk, rest))
    }

    /// Try to downcast a custom value to a specific type.
    ///
    /// Returns `None` if this is not a `Custom` variant or if the type doesn't match.
    #[inline]
    pub fn downcast_custom<T: 'static>(&self) -> Option<&T> {
        match self {
            KlujurVal::Custom(c) => c.downcast_ref::<T>(),
            _ => None,
        }
    }

    /// Create a sorted map with a custom comparator
    #[inline]
    pub fn sorted_map_by(comparator: KlujurVal) -> Self {
        KlujurVal::SortedMapBy(KlujurSortedMapBy::new(comparator))
    }

    /// Create a sorted set with a custom comparator
    #[inline]
    pub fn sorted_set_by(comparator: KlujurVal) -> Self {
        KlujurVal::SortedSetBy(KlujurSortedSetBy::new(comparator))
    }

    /// Get the metadata of this value, if any.
    /// Returns None for types that don't support metadata.
    #[inline]
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
    #[inline]
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
            KlujurVal::BigInt(n) => write!(f, "{}N", n),
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
            KlujurVal::BigRatio(num, den) => write!(f, "{}/{}N", num, den),
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
            KlujurVal::Chunk(ch) => write!(f, "{}", ch),
            KlujurVal::ChunkBuffer(cb) => write!(f, "{}", cb),
            KlujurVal::ChunkedSeq(cs) => write!(f, "{}", cs),
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

// # Float and NaN Handling in Collections
//
// Unlike IEEE 754 (where NaN != NaN), Klujur treats NaN values as equal to
// themselves. This is required for correct behaviour in collections:
//
// - **Hash/Eq contract**: If two values are equal, they must hash identically.
//   Since NaN can be used as a map key, NaN must equal itself.
//
// - **Total ordering**: For sorted collections, all values must be orderable.
//   NaN values compare equal to each other.
//
// - **Multiple NaN bit patterns**: IEEE 754 defines many valid NaN bit patterns.
//   All are normalised to `f64::NAN.to_bits()` for consistent hashing/equality.
//
// This matches Clojure's behaviour where `(= ##NaN ##NaN)` returns true.

/// Normalize float bits for consistent hashing and equality.
///
/// Handles two special cases to satisfy the Hash/Eq contract:
///
/// 1. **NaN normalisation**: Multiple NaN bit patterns exist in IEEE 754.
///    All NaN values are mapped to a single canonical representation so they
///    hash identically and compare equal when used as map keys or set elements.
///
/// 2. **Zero normalisation**: IEEE 754 distinguishes +0.0 and -0.0, but they
///    compare equal. Both are mapped to the same bits for consistent hashing.
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

/// Compare two sequential values (List, Vector, or realized LazySeq) element by element.
/// Returns None if either value is not sequential or if a LazySeq is not realized.
fn seqs_equal(a: &KlujurVal, b: &KlujurVal) -> Option<bool> {
    fn get_seq_iter(val: &KlujurVal) -> Option<(Vec<KlujurVal>, bool)> {
        // Returns (elements, is_complete) where is_complete indicates we have all elements
        match val {
            KlujurVal::Nil => Some((vec![], true)),
            KlujurVal::List(items, _) => Some((items.iter().cloned().collect(), true)),
            KlujurVal::Vector(items, _) => Some((items.iter().cloned().collect(), true)),
            KlujurVal::LazySeq(_) => {
                // Only compare realized lazy sequences
                let mut elements = vec![];
                let mut current = val.clone();
                loop {
                    match &current {
                        KlujurVal::Nil => return Some((elements, true)),
                        KlujurVal::List(items, _) if items.is_empty() => {
                            return Some((elements, true));
                        }
                        KlujurVal::List(items, _) => {
                            elements.extend(items.iter().cloned());
                            return Some((elements, true));
                        }
                        KlujurVal::Vector(items, _) if items.is_empty() => {
                            return Some((elements, true));
                        }
                        KlujurVal::Vector(items, _) => {
                            elements.extend(items.iter().cloned());
                            return Some((elements, true));
                        }
                        KlujurVal::LazySeq(inner_ls) => {
                            if let Some(result) = inner_ls.get_cached() {
                                match result {
                                    SeqResult::Empty => return Some((elements, true)),
                                    SeqResult::Cons(first, rest) => {
                                        elements.push(first);
                                        current = rest;
                                    }
                                }
                            } else {
                                // Not realized - can't compare
                                return None;
                            }
                        }
                        _ => return Some((elements, true)),
                    }
                }
            }
            _ => None,
        }
    }

    let (a_elems, _) = get_seq_iter(a)?;
    let (b_elems, _) = get_seq_iter(b)?;

    if a_elems.len() != b_elems.len() {
        return Some(false);
    }

    for (x, y) in a_elems.iter().zip(b_elems.iter()) {
        if x != y {
            return Some(false);
        }
    }

    Some(true)
}

impl PartialEq for KlujurVal {
    fn eq(&self, other: &Self) -> bool {
        // Note: Metadata is intentionally ignored in equality comparisons.
        // (= [1 2] (with-meta [1 2] {:a 1})) => true
        match (self, other) {
            (KlujurVal::Nil, KlujurVal::Nil) => true,
            (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a == b,
            (KlujurVal::Int(a), KlujurVal::Int(b)) => a == b,
            (KlujurVal::BigInt(a), KlujurVal::BigInt(b)) => a == b,
            // BigInt-Int equality: compare by converting Int to BigInt
            (KlujurVal::BigInt(a), KlujurVal::Int(b)) => *a == BigInt::from(*b),
            (KlujurVal::Int(a), KlujurVal::BigInt(b)) => BigInt::from(*a) == *b,
            (KlujurVal::Float(a), KlujurVal::Float(b)) => {
                normalize_float_bits(*a) == normalize_float_bits(*b)
            }
            // For Int/Float equality, we need to be careful about precision loss.
            // f64 can only exactly represent integers up to 2^53.
            // For larger integers, we check if the float can be exactly represented
            // as that integer (round-trip check).
            (KlujurVal::Int(a), KlujurVal::Float(b)) => {
                // Check if float has a fractional part
                if b.fract() != 0.0 || b.is_nan() || b.is_infinite() {
                    return false;
                }
                // Convert float to int and check round-trip
                let b_as_int = *b as i64;
                *a == b_as_int && (b_as_int as f64) == *b
            }
            (KlujurVal::Float(a), KlujurVal::Int(b)) => {
                // Check if float has a fractional part
                if a.fract() != 0.0 || a.is_nan() || a.is_infinite() {
                    return false;
                }
                // Convert float to int and check round-trip
                let a_as_int = *a as i64;
                a_as_int == *b && (a_as_int as f64) == *a
            }
            // BigInt-Float equality: convert BigInt to f64 and compare
            (KlujurVal::BigInt(a), KlujurVal::Float(b)) => a
                .to_f64()
                .is_some_and(|af| normalize_float_bits(af) == normalize_float_bits(*b)),
            (KlujurVal::Float(a), KlujurVal::BigInt(b)) => b
                .to_f64()
                .is_some_and(|bf| normalize_float_bits(*a) == normalize_float_bits(bf)),
            (KlujurVal::Ratio(an, ad), KlujurVal::Ratio(bn, bd)) => an == bn && ad == bd,
            (KlujurVal::BigRatio(an, ad), KlujurVal::BigRatio(bn, bd)) => an == bn && ad == bd,
            // Ratio-Int equality: a/b == c iff a == b*c (after normalisation, so gcd(a,b)=1)
            (KlujurVal::Ratio(num, den), KlujurVal::Int(n)) => *den == 1 && *num == *n,
            (KlujurVal::Int(n), KlujurVal::Ratio(num, den)) => *den == 1 && *num == *n,
            // BigRatio-BigInt equality
            (KlujurVal::BigRatio(num, den), KlujurVal::BigInt(n)) => {
                den == &BigInt::from(1) && num == n
            }
            (KlujurVal::BigInt(n), KlujurVal::BigRatio(num, den)) => {
                den == &BigInt::from(1) && num == n
            }
            // Cross-precision ratio equality
            (KlujurVal::BigRatio(an, ad), KlujurVal::Ratio(bn, bd)) => {
                *an == BigInt::from(*bn) && *ad == BigInt::from(*bd)
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::BigRatio(bn, bd)) => {
                BigInt::from(*an) == *bn && BigInt::from(*ad) == *bd
            }
            // BigRatio-Int equality
            (KlujurVal::BigRatio(num, den), KlujurVal::Int(n)) => {
                den == &BigInt::from(1) && num == &BigInt::from(*n)
            }
            (KlujurVal::Int(n), KlujurVal::BigRatio(num, den)) => {
                den == &BigInt::from(1) && num == &BigInt::from(*n)
            }
            // Ratio-BigInt equality
            (KlujurVal::Ratio(num, den), KlujurVal::BigInt(n)) => {
                *den == 1 && BigInt::from(*num) == *n
            }
            (KlujurVal::BigInt(n), KlujurVal::Ratio(num, den)) => {
                *den == 1 && *n == BigInt::from(*num)
            }
            // Ratio-Float equality: convert ratio to float and compare
            (KlujurVal::Ratio(num, den), KlujurVal::Float(f)) => {
                normalize_float_bits(*num as f64 / *den as f64) == normalize_float_bits(*f)
            }
            (KlujurVal::Float(f), KlujurVal::Ratio(num, den)) => {
                normalize_float_bits(*f) == normalize_float_bits(*num as f64 / *den as f64)
            }
            // BigRatio-Float equality
            (KlujurVal::BigRatio(num, den), KlujurVal::Float(f)) => num
                .to_f64()
                .zip(den.to_f64())
                .is_some_and(|(nf, df)| normalize_float_bits(nf / df) == normalize_float_bits(*f)),
            (KlujurVal::Float(f), KlujurVal::BigRatio(num, den)) => num
                .to_f64()
                .zip(den.to_f64())
                .is_some_and(|(nf, df)| normalize_float_bits(*f) == normalize_float_bits(nf / df)),
            (KlujurVal::Char(a), KlujurVal::Char(b)) => a == b,
            (KlujurVal::String(a), KlujurVal::String(b)) => a == b,
            (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a == b, // ignore metadata
            (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a == b,
            (KlujurVal::List(a, _), KlujurVal::List(b, _)) => a == b, // ignore metadata
            (KlujurVal::Vector(a, _), KlujurVal::Vector(b, _)) => a == b, // ignore metadata
            // Cross-type sequential equality (Clojure: (= '(1 2) [1 2]) => true)
            (KlujurVal::List(a, _), KlujurVal::Vector(b, _)) => a == b,
            (KlujurVal::Vector(a, _), KlujurVal::List(b, _)) => a == b,
            // LazySeq cross-type equality (only for realized lazy seqs)
            (KlujurVal::LazySeq(_), KlujurVal::List(_, _))
            | (KlujurVal::List(_, _), KlujurVal::LazySeq(_))
            | (KlujurVal::LazySeq(_), KlujurVal::Vector(_, _))
            | (KlujurVal::Vector(_, _), KlujurVal::LazySeq(_)) => {
                seqs_equal(self, other).unwrap_or(false)
            }
            (KlujurVal::Map(a, _), KlujurVal::Map(b, _)) => a == b, // ignore metadata
            (KlujurVal::Set(a, _), KlujurVal::Set(b, _)) => a == b, // ignore metadata
            (KlujurVal::Fn(a), KlujurVal::Fn(b)) => a == b,
            (KlujurVal::NativeFn(a), KlujurVal::NativeFn(b)) => a == b,
            (KlujurVal::Macro(a), KlujurVal::Macro(b)) => a == b,
            (KlujurVal::Var(a), KlujurVal::Var(b)) => a == b,
            (KlujurVal::Atom(a), KlujurVal::Atom(b)) => a == b,
            (KlujurVal::Delay(a), KlujurVal::Delay(b)) => a == b,
            // LazySeq: use seqs_equal for value-based comparison
            (KlujurVal::LazySeq(a), KlujurVal::LazySeq(b)) => {
                // Fast path: same reference
                if Rc::ptr_eq(a.state(), b.state()) {
                    return true;
                }
                // Compare by elements (only works for realized seqs)
                seqs_equal(self, other).unwrap_or(false)
            }
            (KlujurVal::Multimethod(a), KlujurVal::Multimethod(b)) => a == b,
            (KlujurVal::Hierarchy(a), KlujurVal::Hierarchy(b)) => Rc::ptr_eq(a, b),
            (KlujurVal::Reduced(a), KlujurVal::Reduced(b)) => a == b,
            (KlujurVal::Volatile(a), KlujurVal::Volatile(b)) => a == b,
            (KlujurVal::Protocol(a), KlujurVal::Protocol(b)) => a == b,
            (KlujurVal::Record(a), KlujurVal::Record(b)) => a == b,
            (KlujurVal::SortedMapBy(a), KlujurVal::SortedMapBy(b)) => a == b,
            (KlujurVal::SortedSetBy(a), KlujurVal::SortedSetBy(b)) => a == b,
            (KlujurVal::Custom(a), KlujurVal::Custom(b)) => a == b,
            (KlujurVal::Chunk(a), KlujurVal::Chunk(b)) => a == b,
            (KlujurVal::ChunkBuffer(a), KlujurVal::ChunkBuffer(b)) => a == b,
            (KlujurVal::ChunkedSeq(a), KlujurVal::ChunkedSeq(b)) => a == b,
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
                KlujurVal::BigInt(_) => 2, // Same as Int for numeric comparison
                KlujurVal::Float(_) => 2,  // Same as Int for numeric comparison
                KlujurVal::Ratio(_, _) => 2,
                KlujurVal::BigRatio(_, _) => 2,
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
                KlujurVal::Chunk(_) => 27,
                KlujurVal::ChunkBuffer(_) => 28,
                KlujurVal::ChunkedSeq(_) => 29,
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
            // Numeric comparisons - all numeric types compare to each other
            (KlujurVal::Int(a), KlujurVal::Int(b)) => a.cmp(b),
            (KlujurVal::BigInt(a), KlujurVal::BigInt(b)) => a.cmp(b),
            (KlujurVal::Int(a), KlujurVal::BigInt(b)) => BigInt::from(*a).cmp(b),
            (KlujurVal::BigInt(a), KlujurVal::Int(b)) => a.cmp(&BigInt::from(*b)),
            (KlujurVal::Float(a), KlujurVal::Float(b)) => {
                // Use normalized bits for total ordering (NaN sorts equal to itself)
                normalize_float_bits(*a).cmp(&normalize_float_bits(*b))
            }
            (KlujurVal::Int(a), KlujurVal::Float(b)) => {
                normalize_float_bits(*a as f64).cmp(&normalize_float_bits(*b))
            }
            (KlujurVal::Float(a), KlujurVal::Int(b)) => {
                normalize_float_bits(*a).cmp(&normalize_float_bits(*b as f64))
            }
            (KlujurVal::BigInt(a), KlujurVal::Float(b)) => {
                let af = a.to_f64().unwrap_or(f64::INFINITY);
                normalize_float_bits(af).cmp(&normalize_float_bits(*b))
            }
            (KlujurVal::Float(a), KlujurVal::BigInt(b)) => {
                let bf = b.to_f64().unwrap_or(f64::INFINITY);
                normalize_float_bits(*a).cmp(&normalize_float_bits(bf))
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::Ratio(bn, bd)) => {
                // Cross multiply to compare: an/ad vs bn/bd => an*bd vs bn*ad
                // Use i128 to avoid overflow
                ((*an as i128) * (*bd as i128)).cmp(&((*bn as i128) * (*ad as i128)))
            }
            (KlujurVal::BigRatio(an, ad), KlujurVal::BigRatio(bn, bd)) => {
                // Cross multiply to compare: an/ad vs bn/bd => an*bd vs bn*ad
                (an * bd).cmp(&(bn * ad))
            }
            // Cross-precision ratio comparisons
            (KlujurVal::Ratio(an, ad), KlujurVal::BigRatio(bn, bd)) => {
                let an_big = BigInt::from(*an);
                let ad_big = BigInt::from(*ad);
                (&an_big * bd).cmp(&(bn * &ad_big))
            }
            (KlujurVal::BigRatio(an, ad), KlujurVal::Ratio(bn, bd)) => {
                let bn_big = BigInt::from(*bn);
                let bd_big = BigInt::from(*bd);
                (an * &bd_big).cmp(&(&bn_big * ad))
            }
            // Int-Ratio comparisons
            (KlujurVal::Int(a), KlujurVal::Ratio(bn, bd)) => {
                ((*a as i128) * (*bd as i128)).cmp(&(*bn as i128))
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::Int(b)) => {
                (*an as i128).cmp(&((*b as i128) * (*ad as i128)))
            }
            // BigInt-Ratio comparisons
            (KlujurVal::BigInt(a), KlujurVal::Ratio(bn, bd)) => {
                (a * BigInt::from(*bd)).cmp(&BigInt::from(*bn))
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::BigInt(b)) => {
                BigInt::from(*an).cmp(&(b * BigInt::from(*ad)))
            }
            // Int-BigRatio comparisons
            (KlujurVal::Int(a), KlujurVal::BigRatio(bn, bd)) => (BigInt::from(*a) * bd).cmp(bn),
            (KlujurVal::BigRatio(an, ad), KlujurVal::Int(b)) => an.cmp(&(BigInt::from(*b) * ad)),
            // BigInt-BigRatio comparisons
            (KlujurVal::BigInt(a), KlujurVal::BigRatio(bn, bd)) => (a * bd).cmp(bn),
            (KlujurVal::BigRatio(an, ad), KlujurVal::BigInt(b)) => an.cmp(&(b * ad)),
            // Float-Ratio comparisons
            (KlujurVal::Float(a), KlujurVal::Ratio(bn, bd)) => {
                normalize_float_bits(*a).cmp(&normalize_float_bits(*bn as f64 / *bd as f64))
            }
            (KlujurVal::Ratio(an, ad), KlujurVal::Float(b)) => {
                normalize_float_bits(*an as f64 / *ad as f64).cmp(&normalize_float_bits(*b))
            }
            // Float-BigRatio comparisons
            (KlujurVal::Float(a), KlujurVal::BigRatio(bn, bd)) => {
                let bf = bn
                    .to_f64()
                    .zip(bd.to_f64())
                    .map(|(n, d)| n / d)
                    .unwrap_or(f64::INFINITY);
                normalize_float_bits(*a).cmp(&normalize_float_bits(bf))
            }
            (KlujurVal::BigRatio(an, ad), KlujurVal::Float(b)) => {
                let af = an
                    .to_f64()
                    .zip(ad.to_f64())
                    .map(|(n, d)| n / d)
                    .unwrap_or(f64::INFINITY);
                normalize_float_bits(af).cmp(&normalize_float_bits(*b))
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
            (KlujurVal::Chunk(a), KlujurVal::Chunk(b)) => a.cmp(b),
            (KlujurVal::ChunkBuffer(a), KlujurVal::ChunkBuffer(b)) => a.cmp(b),
            (KlujurVal::ChunkedSeq(a), KlujurVal::ChunkedSeq(b)) => a.cmp(b),
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
            KlujurVal::BigInt(n) => {
                // If BigInt fits in i64, hash identically to Int for consistency
                if let Some(i) = n.to_i64() {
                    hash_numeric(state, Some(i), i as f64);
                } else {
                    // Large BigInt - can never equal Int/Float, use BigInt's hash
                    const BIGINT_DISCRIMINANT: u8 = 1;
                    BIGINT_DISCRIMINANT.hash(state);
                    n.hash(state);
                }
            }
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
            KlujurVal::BigRatio(num, den) => {
                // Check if this equals a simpler numeric type
                if den == &BigInt::from(1) {
                    if let Some(i) = num.to_i64() {
                        // Equals an Int
                        hash_numeric(state, Some(i), i as f64);
                    } else {
                        // Large BigInt numerator
                        const BIGINT_DISCRIMINANT: u8 = 1;
                        BIGINT_DISCRIMINANT.hash(state);
                        num.hash(state);
                    }
                } else {
                    // True ratio - hash as float if possible
                    if let (Some(nf), Some(df)) = (num.to_f64(), den.to_f64()) {
                        hash_numeric(state, None, nf / df);
                    } else {
                        // Large BigRatio - use its own hash
                        const BIGRATIO_DISCRIMINANT: u8 = 2;
                        BIGRATIO_DISCRIMINANT.hash(state);
                        num.hash(state);
                        den.hash(state);
                    }
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
            // List and Vector use a shared discriminant for hashing because they
            // compare equal when they contain the same elements (Clojure semantics:
            // (= '(1 2) [1 2]) => true). This maintains the Hash/Eq contract.
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                const SEQUENTIAL_DISCRIMINANT: u8 = 200;
                SEQUENTIAL_DISCRIMINANT.hash(state);
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
                // LazySeqs can compare equal to List/Vector when realized via seqs_equal.
                // To maintain the Hash/Eq contract for realized lazy seqs, we attempt to
                // hash by value using the same discriminant as List/Vector.
                // For unrealized lazy seqs, we fall back to pointer identity.
                //
                // WARNING: Using LazySeqs as map keys is discouraged because:
                // 1. Unrealized lazy seqs hash by pointer identity
                // 2. Realizing a lazy seq doesn't change its hash
                // 3. This can lead to Hash/Eq inconsistency
                if let Some(result) = ls.get_cached() {
                    // Realized - hash by value like List/Vector
                    const SEQUENTIAL_DISCRIMINANT: u8 = 200;
                    SEQUENTIAL_DISCRIMINANT.hash(state);
                    // Hash elements
                    let mut current_result = result;
                    loop {
                        match current_result {
                            SeqResult::Empty => break,
                            SeqResult::Cons(first, rest) => {
                                first.hash(state);
                                // Try to continue with rest
                                match &rest {
                                    KlujurVal::LazySeq(rest_ls) => {
                                        if let Some(r) = rest_ls.get_cached() {
                                            current_result = r;
                                        } else {
                                            // Rest not realized, hash remaining by pointer
                                            (Rc::as_ptr(rest_ls.state()) as usize).hash(state);
                                            break;
                                        }
                                    }
                                    KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                                        items.hash(state);
                                        break;
                                    }
                                    KlujurVal::Nil => break,
                                    other => {
                                        other.hash(state);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    // Unrealized - hash by pointer identity
                    std::mem::discriminant(self).hash(state);
                    (Rc::as_ptr(ls.state()) as usize).hash(state);
                }
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
            KlujurVal::Chunk(ch) => {
                std::mem::discriminant(self).hash(state);
                ch.hash(state);
            }
            KlujurVal::ChunkBuffer(cb) => {
                std::mem::discriminant(self).hash(state);
                cb.hash(state);
            }
            KlujurVal::ChunkedSeq(cs) => {
                std::mem::discriminant(self).hash(state);
                cs.hash(state);
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

impl From<BigInt> for KlujurVal {
    fn from(n: BigInt) -> Self {
        KlujurVal::bigint(n)
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

#[cfg(test)]
mod size_tests {
    use super::*;

    #[test]
    fn test_klujur_val_size() {
        use std::mem::size_of;

        let size = size_of::<KlujurVal>();
        eprintln!("size_of::<KlujurVal>() = {} bytes", size);

        // Print sizes of common Rust types for reference
        eprintln!("size_of::<i64>() = {} bytes", size_of::<i64>());
        eprintln!("size_of::<f64>() = {} bytes", size_of::<f64>());
        eprintln!("size_of::<Rc<str>>() = {} bytes", size_of::<Rc<str>>());
        eprintln!(
            "size_of::<Vector<KlujurVal>>() = {} bytes",
            size_of::<Vector<KlujurVal>>()
        );
        eprintln!(
            "size_of::<OrdMap<KlujurVal, KlujurVal>>() = {} bytes",
            size_of::<OrdMap<KlujurVal, KlujurVal>>()
        );
        eprintln!(
            "size_of::<Option<Rc<Meta>>>() = {} bytes",
            size_of::<Option<Rc<Meta>>>()
        );
        eprintln!("size_of::<BigInt>() = {} bytes", size_of::<BigInt>());
        eprintln!("size_of::<Symbol>() = {} bytes", size_of::<Symbol>());
        eprintln!("size_of::<Keyword>() = {} bytes", size_of::<Keyword>());

        // The enum size is determined by its largest variant plus discriminant
        // If the enum is significantly larger than needed, we should consider boxing
        assert!(size > 0, "KlujurVal should have non-zero size");
    }

    #[test]
    fn test_list_vector_hash_eq_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_val(v: &KlujurVal) -> u64 {
            let mut h = DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        }

        // Create a list and vector with the same elements
        let list = KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
        ]);
        let vec = KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
        ]);

        // Per Clojure semantics, they should be equal
        assert_eq!(
            list, vec,
            "List and Vector with same elements should be equal"
        );

        // The Hash/Eq contract requires: a == b implies hash(a) == hash(b)
        assert_eq!(
            hash_val(&list),
            hash_val(&vec),
            "List and Vector that are equal must have the same hash"
        );

        // Empty collections should also satisfy this
        let empty_list = KlujurVal::list(vec![]);
        let empty_vec = KlujurVal::vector(vec![]);
        assert_eq!(empty_list, empty_vec);
        assert_eq!(hash_val(&empty_list), hash_val(&empty_vec));

        // Different contents should (usually) have different hashes
        let different_vec = KlujurVal::vector(vec![KlujurVal::int(4), KlujurVal::int(5)]);
        assert_ne!(list, different_vec);
        // Note: hash collision is possible but very unlikely with different contents
    }
}
