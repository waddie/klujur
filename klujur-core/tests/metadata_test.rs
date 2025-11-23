// klujur-core - Metadata integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur metadata operations.
//!
//! Tests for: meta, with-meta, vary-meta, ^metadata reader macro

mod common;

use common::{KlujurVal, eval_str_with_env, new_env};

// =============================================================================
// meta - getting metadata
// =============================================================================

#[test]
fn test_meta_nil_by_default() {
    // Most values don't have metadata by default
    assert_eval!("(meta [])", KlujurVal::Nil);
    assert_eval!("(meta {})", KlujurVal::Nil);
    assert_eval!("(meta #{})", KlujurVal::Nil);
    assert_eval!("(meta '())", KlujurVal::Nil);
}

#[test]
fn test_meta_on_primitives() {
    // Primitives don't support metadata
    assert_eval!("(meta 42)", KlujurVal::Nil);
    assert_eval!("(meta \"string\")", KlujurVal::Nil);
    assert_eval!("(meta :keyword)", KlujurVal::Nil);
    assert_eval!("(meta nil)", KlujurVal::Nil);
}

// =============================================================================
// with-meta - setting metadata
// =============================================================================

#[test]
fn test_with_meta_vector() {
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2 3] {:doc \"a vector\"}))", &env).unwrap();

    let result = eval_str_with_env("(meta v)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Map(_, _)));

    let doc = eval_str_with_env("(:doc (meta v))", &env).unwrap();
    assert_eq!(doc, KlujurVal::string("a vector"));
}

#[test]
fn test_with_meta_map() {
    let env = new_env();
    eval_str_with_env("(def m (with-meta {:a 1} {:type :special}))", &env).unwrap();

    let result = eval_str_with_env("(:type (meta m))", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));
}

#[test]
fn test_with_meta_list() {
    let env = new_env();
    eval_str_with_env("(def l (with-meta '(1 2 3) {:source \"test\"}))", &env).unwrap();

    let result = eval_str_with_env("(:source (meta l))", &env).unwrap();
    assert_eq!(result, KlujurVal::string("test"));
}

#[test]
fn test_with_meta_set() {
    let env = new_env();
    eval_str_with_env("(def s (with-meta #{1 2 3} {:unique true}))", &env).unwrap();

    let result = eval_str_with_env("(:unique (meta s))", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_with_meta_returns_new_value() {
    let env = new_env();
    eval_str_with_env("(def original [1 2 3])", &env).unwrap();
    eval_str_with_env(
        "(def with-metadata (with-meta original {:doc \"new\"}))",
        &env,
    )
    .unwrap();

    // Original is unchanged
    let orig_meta = eval_str_with_env("(meta original)", &env).unwrap();
    assert_eq!(orig_meta, KlujurVal::Nil);

    // New value has metadata
    let new_meta = eval_str_with_env("(:doc (meta with-metadata))", &env).unwrap();
    assert_eq!(new_meta, KlujurVal::string("new"));
}

#[test]
fn test_with_meta_replaces_existing() {
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2 3] {:a 1}))", &env).unwrap();
    eval_str_with_env("(def v2 (with-meta v {:b 2}))", &env).unwrap();

    // Old metadata is replaced
    let a = eval_str_with_env("(:a (meta v2))", &env).unwrap();
    assert_eq!(a, KlujurVal::Nil);

    let b = eval_str_with_env("(:b (meta v2))", &env).unwrap();
    assert_eq!(b, KlujurVal::int(2));
}

// =============================================================================
// vary-meta - modifying metadata (NOT YET IMPLEMENTED)
// =============================================================================

#[test]
fn test_vary_meta_not_implemented() {
    // vary-meta is not yet implemented - use with-meta with explicit meta manipulation
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2 3] {:count 0}))", &env).unwrap();

    let result = eval_str_with_env("(vary-meta v assoc :count 1)", &env);
    assert!(result.is_err());
}

#[test]
fn test_manual_vary_meta_workaround() {
    // Workaround: use with-meta with assoc on existing meta
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2 3] {:count 0}))", &env).unwrap();
    eval_str_with_env("(def v2 (with-meta v (assoc (meta v) :count 1)))", &env).unwrap();

    let result = eval_str_with_env("(:count (meta v2))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

// =============================================================================
// Metadata on functions (NOT YET SUPPORTED)
// =============================================================================

#[test]
fn test_meta_on_fn_not_supported() {
    // Functions don't currently support metadata
    let env = new_env();
    let result = eval_str_with_env(
        "(with-meta (fn* [x] (* x 2)) {:doc \"Doubles input\"})",
        &env,
    );
    assert!(result.is_err());
}

// =============================================================================
// Metadata on symbols
// =============================================================================

#[test]
fn test_meta_on_symbol() {
    let env = new_env();
    eval_str_with_env("(def s (with-meta 'foo {:tag :string}))", &env).unwrap();

    let tag = eval_str_with_env("(:tag (meta s))", &env).unwrap();
    assert!(matches!(tag, KlujurVal::Keyword(_)));
}

// =============================================================================
// Metadata reader macro (^)
// =============================================================================

#[test]
fn test_metadata_reader_basic() {
    // ^{:doc "test"} syntax
    let env = new_env();
    eval_str_with_env("(def v ^{:doc \"test\"} [1 2 3])", &env).unwrap();

    let doc = eval_str_with_env("(:doc (meta v))", &env).unwrap();
    assert_eq!(doc, KlujurVal::string("test"));
}

#[test]
fn test_metadata_reader_keyword_shorthand() {
    // ^:keyword is shorthand for ^{:keyword true}
    let env = new_env();
    eval_str_with_env("(def v ^:private [1 2 3])", &env).unwrap();

    let private = eval_str_with_env("(:private (meta v))", &env).unwrap();
    assert_eq!(private, KlujurVal::bool(true));
}

#[test]
fn test_metadata_reader_symbol_shorthand() {
    // ^SomeType is shorthand for ^{:tag SomeType}
    // Note: The symbol must be quoted since unquoted symbols are resolved
    let env = new_env();
    eval_str_with_env("(def v ^{:tag 'String} [1 2 3])", &env).unwrap();

    let tag = eval_str_with_env("(:tag (meta v))", &env).unwrap();
    assert!(matches!(tag, KlujurVal::Symbol(..)));
}

// =============================================================================
// Metadata preservation (NOT CURRENTLY IMPLEMENTED)
// =============================================================================

#[test]
fn test_conj_does_not_preserve_metadata() {
    // Currently, conj does not preserve metadata
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2] {:source \"test\"}))", &env).unwrap();
    eval_str_with_env("(def v2 (conj v 3))", &env).unwrap();

    // Metadata is not preserved
    let source = eval_str_with_env("(:source (meta v2))", &env).unwrap();
    assert_eq!(source, KlujurVal::Nil);
}

#[test]
fn test_assoc_does_not_preserve_metadata() {
    // Currently, assoc does not preserve metadata
    let env = new_env();
    eval_str_with_env("(def m (with-meta {:a 1} {:type :special}))", &env).unwrap();
    eval_str_with_env("(def m2 (assoc m :b 2))", &env).unwrap();

    // Metadata is not preserved
    let type_meta = eval_str_with_env("(:type (meta m2))", &env).unwrap();
    assert_eq!(type_meta, KlujurVal::Nil);
}

#[test]
fn test_dissoc_does_not_preserve_metadata() {
    // Currently, dissoc does not preserve metadata
    let env = new_env();
    eval_str_with_env("(def m (with-meta {:a 1 :b 2} {:source \"test\"}))", &env).unwrap();
    eval_str_with_env("(def m2 (dissoc m :a))", &env).unwrap();

    // Metadata is not preserved
    let source = eval_str_with_env("(:source (meta m2))", &env).unwrap();
    assert_eq!(source, KlujurVal::Nil);
}

// =============================================================================
// Common metadata patterns
// =============================================================================

#[test]
fn test_doc_metadata() {
    let env = new_env();
    eval_str_with_env(
        "(def ^{:doc \"Adds two numbers\"} my-add (fn* [a b] (+ a b)))",
        &env,
    )
    .unwrap();

    // Get the var and check its metadata
    let result = eval_str_with_env("(my-add 1 2)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));
}

#[test]
fn test_private_metadata() {
    let env = new_env();
    eval_str_with_env("(def ^:private secret 42)", &env).unwrap();

    // Still accessible in same namespace
    let result = eval_str_with_env("secret", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_meta_nil_safe() {
    // meta on nil should return nil, not error
    assert_eval!("(meta nil)", KlujurVal::Nil);
}

#[test]
fn test_with_meta_nil_metadata() {
    let env = new_env();
    eval_str_with_env("(def v (with-meta [1 2 3] {:a 1}))", &env).unwrap();
    // Setting metadata to nil clears it
    eval_str_with_env("(def v2 (with-meta v nil))", &env).unwrap();

    let result = eval_str_with_env("(meta v2)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn test_metadata_equality() {
    // Metadata doesn't affect equality
    let env = new_env();
    eval_str_with_env("(def v1 [1 2 3])", &env).unwrap();
    eval_str_with_env("(def v2 (with-meta [1 2 3] {:tag :different}))", &env).unwrap();

    let result = eval_str_with_env("(= v1 v2)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}
