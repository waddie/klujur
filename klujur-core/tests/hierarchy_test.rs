// klujur-core - Hierarchy integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur hierarchy operations.
//!
//! Tests for: derive, underive, isa?, parents, ancestors, descendants

mod common;

use common::{KlujurVal, eval_str_with_env, new_env};

// =============================================================================
// derive - establishing relationships
// =============================================================================

#[test]
fn test_derive_basic() {
    let env = new_env();
    // Derive a keyword from another
    let result = eval_str_with_env("(derive ::child ::parent)", &env);
    assert!(result.is_ok());
}

#[test]
fn test_derive_multiple_parents() {
    let env = new_env();
    eval_str_with_env("(derive ::cat ::animal)", &env).unwrap();
    eval_str_with_env("(derive ::cat ::pet)", &env).unwrap();

    // cat should now be related to both animal and pet
    let result = eval_str_with_env("(isa? ::cat ::animal)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    let result = eval_str_with_env("(isa? ::cat ::pet)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_derive_chain() {
    let env = new_env();
    eval_str_with_env("(derive ::poodle ::dog)", &env).unwrap();
    eval_str_with_env("(derive ::dog ::animal)", &env).unwrap();

    // Transitive: poodle should be an animal
    let result = eval_str_with_env("(isa? ::poodle ::animal)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_derive_self_error() {
    let env = new_env();
    // Cannot derive from self
    let result = eval_str_with_env("(derive ::thing ::thing)", &env);
    assert!(result.is_err());
}

#[test]
fn test_derive_cycle_error() {
    let env = new_env();
    eval_str_with_env("(derive ::a ::b)", &env).unwrap();
    eval_str_with_env("(derive ::b ::c)", &env).unwrap();

    // Creating a cycle should fail
    let result = eval_str_with_env("(derive ::c ::a)", &env);
    assert!(result.is_err());
}

// =============================================================================
// isa? - checking relationships
// =============================================================================

#[test]
fn test_isa_reflexive() {
    // Everything is-a itself
    assert_eval!("(isa? ::thing ::thing)", KlujurVal::bool(true));
    assert_eval!("(isa? :keyword :keyword)", KlujurVal::bool(true));
}

#[test]
fn test_isa_direct_parent() {
    let env = new_env();
    eval_str_with_env("(derive ::child ::parent)", &env).unwrap();

    let result = eval_str_with_env("(isa? ::child ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_isa_transitive() {
    let env = new_env();
    eval_str_with_env("(derive ::grandchild ::child)", &env).unwrap();
    eval_str_with_env("(derive ::child ::parent)", &env).unwrap();

    let result = eval_str_with_env("(isa? ::grandchild ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_isa_false() {
    let env = new_env();
    eval_str_with_env("(derive ::cat ::animal)", &env).unwrap();
    eval_str_with_env("(derive ::dog ::animal)", &env).unwrap();

    // cat is not a dog
    let result = eval_str_with_env("(isa? ::cat ::dog)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));

    // animal is not a cat
    let result = eval_str_with_env("(isa? ::animal ::cat)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

#[test]
fn test_isa_with_vectors() {
    // In Klujur, isa? on vectors doesn't do element-wise checking
    let env = new_env();
    eval_str_with_env("(derive ::child ::parent)", &env).unwrap();

    // Vectors are only equal if identical
    let result = eval_str_with_env("(isa? [::child] [::parent])", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));

    // Same vector is-a itself
    let result = eval_str_with_env("(isa? [::child] [::child])", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// parents - direct parents
// =============================================================================

#[test]
fn test_parents_none() {
    let env = new_env();
    let result = eval_str_with_env("(parents ::orphan)", &env).unwrap();
    // Returns empty set, not nil
    assert!(matches!(result, KlujurVal::Set(_, _)));
    let count = eval_str_with_env("(count (parents ::orphan))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(0));
}

#[test]
fn test_parents_single() {
    let env = new_env();
    eval_str_with_env("(derive ::child ::parent)", &env).unwrap();

    let result = eval_str_with_env("(parents ::child)", &env).unwrap();
    // Should be a set containing ::parent
    assert!(matches!(result, KlujurVal::Set(_, _)));
}

#[test]
fn test_parents_multiple() {
    let env = new_env();
    eval_str_with_env("(derive ::child ::parent1)", &env).unwrap();
    eval_str_with_env("(derive ::child ::parent2)", &env).unwrap();

    let result = eval_str_with_env("(count (parents ::child))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}

// =============================================================================
// ancestors - transitive parents
// =============================================================================

#[test]
fn test_ancestors_none() {
    let env = new_env();
    let result = eval_str_with_env("(ancestors ::orphan)", &env).unwrap();
    // Returns empty set, not nil
    assert!(matches!(result, KlujurVal::Set(_, _)));
    let count = eval_str_with_env("(count (ancestors ::orphan))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(0));
}

#[test]
fn test_ancestors_transitive() {
    let env = new_env();
    eval_str_with_env("(derive ::c ::b)", &env).unwrap();
    eval_str_with_env("(derive ::b ::a)", &env).unwrap();

    // ancestors of ::c should include both ::b and ::a
    let count = eval_str_with_env("(count (ancestors ::c))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(2));

    let has_b = eval_str_with_env("(contains? (ancestors ::c) ::b)", &env).unwrap();
    assert_eq!(has_b, KlujurVal::bool(true));

    let has_a = eval_str_with_env("(contains? (ancestors ::c) ::a)", &env).unwrap();
    assert_eq!(has_a, KlujurVal::bool(true));
}

// =============================================================================
// descendants - transitive children
// =============================================================================

#[test]
fn test_descendants_none() {
    let env = new_env();
    let result = eval_str_with_env("(descendants ::leaf)", &env).unwrap();
    // Returns empty set, not nil
    assert!(matches!(result, KlujurVal::Set(_, _)));
    let count = eval_str_with_env("(count (descendants ::leaf))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(0));
}

#[test]
fn test_descendants_transitive() {
    let env = new_env();
    eval_str_with_env("(derive ::c ::b)", &env).unwrap();
    eval_str_with_env("(derive ::b ::a)", &env).unwrap();

    // descendants of ::a should include both ::b and ::c
    let count = eval_str_with_env("(count (descendants ::a))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(2));

    let has_b = eval_str_with_env("(contains? (descendants ::a) ::b)", &env).unwrap();
    assert_eq!(has_b, KlujurVal::bool(true));

    let has_c = eval_str_with_env("(contains? (descendants ::a) ::c)", &env).unwrap();
    assert_eq!(has_c, KlujurVal::bool(true));
}

// =============================================================================
// underive - removing relationships
// =============================================================================

#[test]
fn test_underive_basic() {
    let env = new_env();
    eval_str_with_env("(derive ::child ::parent)", &env).unwrap();

    // Verify relationship exists
    let result = eval_str_with_env("(isa? ::child ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    // Remove it
    eval_str_with_env("(underive ::child ::parent)", &env).unwrap();

    // Verify relationship is gone
    let result = eval_str_with_env("(isa? ::child ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

#[test]
fn test_underive_updates_ancestors() {
    let env = new_env();
    eval_str_with_env("(derive ::c ::b)", &env).unwrap();
    eval_str_with_env("(derive ::b ::a)", &env).unwrap();

    // c is-a a transitively
    let result = eval_str_with_env("(isa? ::c ::a)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    // Remove middle link
    eval_str_with_env("(underive ::b ::a)", &env).unwrap();

    // c is no longer an a
    let result = eval_str_with_env("(isa? ::c ::a)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));

    // But c is still a b
    let result = eval_str_with_env("(isa? ::c ::b)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_underive_nonexistent() {
    let env = new_env();
    // Underiving a non-existent relationship should be a no-op
    let result = eval_str_with_env("(underive ::x ::y)", &env);
    assert!(result.is_ok());
}

// =============================================================================
// Diamond inheritance
// =============================================================================

#[test]
fn test_diamond_hierarchy() {
    let env = new_env();
    //       animal
    //      /      \
    //    pet     wild
    //      \      /
    //       cat
    eval_str_with_env("(derive ::pet ::animal)", &env).unwrap();
    eval_str_with_env("(derive ::wild ::animal)", &env).unwrap();
    eval_str_with_env("(derive ::cat ::pet)", &env).unwrap();
    eval_str_with_env("(derive ::cat ::wild)", &env).unwrap();

    // cat is an animal (through both paths)
    let result = eval_str_with_env("(isa? ::cat ::animal)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    // cat has 3 ancestors: pet, wild, animal
    let count = eval_str_with_env("(count (ancestors ::cat))", &env).unwrap();
    assert_eq!(count, KlujurVal::int(3));
}

// =============================================================================
// Hierarchy with non-keyword values
// =============================================================================

#[test]
fn test_derive_with_symbols() {
    let env = new_env();
    eval_str_with_env("(derive 'child 'parent)", &env).unwrap();

    let result = eval_str_with_env("(isa? 'child 'parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

// =============================================================================
// make-hierarchy - custom hierarchies
// =============================================================================

#[test]
fn test_make_hierarchy() {
    let env = new_env();
    let result = eval_str_with_env("(make-hierarchy)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Hierarchy(_)));
}

#[test]
fn test_derive_with_custom_hierarchy() {
    let env = new_env();
    eval_str_with_env("(def h (make-hierarchy))", &env).unwrap();
    eval_str_with_env("(def h (derive h ::child ::parent))", &env).unwrap();

    // Custom hierarchy has the relationship
    let result = eval_str_with_env("(isa? h ::child ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));

    // Global hierarchy doesn't
    let result = eval_str_with_env("(isa? ::child ::parent)", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(false));
}

// =============================================================================
// Multimethod dispatch integration
// =============================================================================

#[test]
fn test_hierarchy_with_multimethod() {
    let env = new_env();
    eval_str_with_env("(derive ::rectangle ::shape)", &env).unwrap();
    eval_str_with_env("(derive ::square ::rectangle)", &env).unwrap();

    eval_str_with_env("(defmulti area :type)", &env).unwrap();
    eval_str_with_env("(defmethod area ::shape [s] :generic-shape)", &env).unwrap();

    // square should dispatch to ::shape method via hierarchy
    let result = eval_str_with_env("(area {:type ::square})", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));
}
