// klujur-core - Multimethod integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur multimethods.
//!
//! Tests for: defmulti, defmethod, methods, get-method, remove-method, prefer-method

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{KlujurVal, Parser};

/// Helper to evaluate multiple expressions in shared env and return the last result.
fn eval_forms(forms: &[&str]) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_forms_with_env(forms, &env)
}

fn eval_forms_with_env(forms: &[&str], env: &Env) -> Result<KlujurVal, String> {
    let mut result = KlujurVal::Nil;
    for form in forms {
        let mut parser = Parser::new(form).map_err(|e| e.to_string())?;
        if let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
            result = eval(&expr, env).map_err(|e| e.to_string())?;
        }
    }
    Ok(result)
}

/// Helper to evaluate a string and return the result.
fn eval_str(s: &str) -> Result<KlujurVal, String> {
    eval_forms(&[s])
}

/// Assert that evaluating forms produces the expected value.
macro_rules! assert_eval_forms {
    ($forms:expr, $expected:expr) => {
        let result = eval_forms($forms);
        assert!(
            result.is_ok(),
            "Failed to evaluate forms: {:?}",
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation did not match expected"
        );
    };
}

/// Assert that evaluating forms produces an error.
macro_rules! assert_eval_forms_err {
    ($forms:expr) => {
        let result = eval_forms($forms);
        assert!(result.is_err(), "Expected error but got {:?}", result.ok());
    };
}

// =============================================================================
// Basic defmulti/defmethod
// =============================================================================

#[test]
fn test_defmulti_creates_var() {
    let result = eval_forms(&["(defmulti greeting :language)", "(var? (var greeting))"]);
    assert_eq!(result.unwrap(), KlujurVal::Bool(true));
}

#[test]
fn test_basic_keyword_dispatch() {
    assert_eval_forms!(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :french [_] \"Bonjour!\")",
            "(greeting {:language :english})",
        ],
        KlujurVal::string("Hello!")
    );
}

#[test]
fn test_dispatch_to_different_methods() {
    let env = Env::new();
    register_builtins(&env);

    // Define multimethod and methods
    eval_forms_with_env(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :french [_] \"Bonjour!\")",
            "(defmethod greeting :german [_] \"Guten Tag!\")",
        ],
        &env,
    )
    .unwrap();

    // Test each dispatch
    assert_eq!(
        eval_forms_with_env(&["(greeting {:language :english})"], &env).unwrap(),
        KlujurVal::string("Hello!")
    );
    assert_eq!(
        eval_forms_with_env(&["(greeting {:language :french})"], &env).unwrap(),
        KlujurVal::string("Bonjour!")
    );
    assert_eq!(
        eval_forms_with_env(&["(greeting {:language :german})"], &env).unwrap(),
        KlujurVal::string("Guten Tag!")
    );
}

// =============================================================================
// Default method
// =============================================================================

#[test]
fn test_default_method() {
    assert_eval_forms!(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :default [_] \"Hi!\")",
            "(greeting {:language :unknown})",
        ],
        KlujurVal::string("Hi!")
    );
}

#[test]
fn test_default_not_used_when_match_exists() {
    assert_eval_forms!(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :default [_] \"Hi!\")",
            "(greeting {:language :english})",
        ],
        KlujurVal::string("Hello!")
    );
}

#[test]
fn test_no_method_error_without_default() {
    assert_eval_forms_err!(&[
        "(defmulti greeting :language)",
        "(defmethod greeting :english [_] \"Hello!\")",
        "(greeting {:language :unknown})",
    ]);
}

// =============================================================================
// Complex dispatch functions
// =============================================================================

#[test]
fn test_dispatch_on_function() {
    assert_eval_forms!(
        &[
            "(defmulti area (fn [shape] (:shape shape)))",
            "(defmethod area :circle [{:keys [radius]}] (* 3.14 radius radius))",
            "(defmethod area :rectangle [{:keys [width height]}] (* width height))",
            "(area {:shape :rectangle :width 3 :height 4})",
        ],
        KlujurVal::int(12)
    );
}

#[test]
fn test_dispatch_on_vector() {
    assert_eval_forms!(
        &[
            "(defmulti encounter (fn [x y] [(:type x) (:type y)]))",
            "(defmethod encounter [:bunny :lion] [b l] \"run!\")",
            "(defmethod encounter [:lion :bunny] [l b] \"eat\")",
            "(defmethod encounter :default [x y] \"ignore\")",
            "(encounter {:type :bunny} {:type :lion})",
        ],
        KlujurVal::string("run!")
    );
}

// =============================================================================
// Helper functions
// =============================================================================

#[test]
fn test_methods_returns_method_table() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :french [_] \"Bonjour!\")",
        ],
        &env,
    )
    .unwrap();

    // methods should return a map
    let result = eval_forms_with_env(&["(count (methods greeting))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}

#[test]
fn test_get_method_returns_function() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
        ],
        &env,
    )
    .unwrap();

    // get-method should return the function
    let result = eval_forms_with_env(&["(fn? (get-method greeting :english))"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(true));

    // get-method returns nil for missing dispatch value
    let result = eval_forms_with_env(&["(get-method greeting :unknown)"], &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn test_remove_method() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti greeting :language)",
            "(defmethod greeting :english [_] \"Hello!\")",
            "(defmethod greeting :default [_] \"Hi!\")",
        ],
        &env,
    )
    .unwrap();

    // Before removal
    let result = eval_forms_with_env(&["(greeting {:language :english})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hello!"));

    // Remove the method
    eval_forms_with_env(&["(remove-method greeting :english)"], &env).unwrap();

    // After removal, falls back to default
    let result = eval_forms_with_env(&["(greeting {:language :english})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hi!"));
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_defmulti_requires_name() {
    let result = eval_str("(defmulti)");
    assert!(result.is_err());
}

#[test]
fn test_defmulti_requires_dispatch_fn() {
    let result = eval_str("(defmulti foo)");
    assert!(result.is_err());
}

#[test]
fn test_defmethod_requires_params() {
    let result = eval_forms(&["(defmulti foo identity)", "(defmethod foo :bar)"]);
    assert!(result.is_err());
}

#[test]
fn test_method_receives_original_args() {
    // The method should receive the original args, not the dispatch value
    assert_eval_forms!(
        &[
            "(defmulti process :type)",
            "(defmethod process :inc [{:keys [value]}] (inc value))",
            "(process {:type :inc :value 41})",
        ],
        KlujurVal::int(42)
    );
}

// =============================================================================
// Hierarchy support
// =============================================================================

#[test]
fn test_derive_establishes_relationship() {
    assert_eval_forms!(
        &["(derive ::dog ::animal)", "(isa? ::dog ::animal)",],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_isa_reflexive() {
    // isa? is reflexive - everything is itself
    assert_eval_forms!(&["(isa? ::dog ::dog)"], KlujurVal::Bool(true));
}

#[test]
fn test_derive_transitive() {
    assert_eval_forms!(
        &[
            "(derive ::poodle ::dog)",
            "(derive ::dog ::animal)",
            "(isa? ::poodle ::animal)",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_make_hierarchy() {
    assert_eval_forms!(
        &[
            "(def h (make-hierarchy))",
            "(derive h ::cat ::animal)",
            "(isa? h ::cat ::animal)",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_custom_hierarchy_isolated() {
    // Custom hierarchy is isolated from global
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &["(def h (make-hierarchy))", "(derive h ::cat ::animal)"],
        &env,
    )
    .unwrap();

    // In custom hierarchy
    let result = eval_forms_with_env(&["(isa? h ::cat ::animal)"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(true));

    // In global hierarchy (not derived there)
    let result = eval_forms_with_env(&["(isa? ::cat ::animal)"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(false));
}

#[test]
fn test_parents_returns_direct_parents() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(def h (make-hierarchy))",
            "(derive h ::dog ::animal)",
            "(derive h ::dog ::pet)",
        ],
        &env,
    )
    .unwrap();

    let result = eval_forms_with_env(&["(count (parents h ::dog))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(2));
}

#[test]
fn test_ancestors_returns_all_ancestors() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(def h (make-hierarchy))",
            "(derive h ::poodle ::dog)",
            "(derive h ::dog ::animal)",
            "(derive h ::animal ::living-thing)",
        ],
        &env,
    )
    .unwrap();

    // poodle should have 3 ancestors: dog, animal, living-thing
    let result = eval_forms_with_env(&["(count (ancestors h ::poodle))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));
}

#[test]
fn test_descendants_returns_all_descendants() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(def h (make-hierarchy))",
            "(derive h ::poodle ::dog)",
            "(derive h ::labrador ::dog)",
            "(derive h ::dog ::animal)",
        ],
        &env,
    )
    .unwrap();

    // animal should have 3 descendants: dog, poodle, labrador
    let result = eval_forms_with_env(&["(count (descendants h ::animal))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));
}

#[test]
fn test_multimethod_with_hierarchy_dispatch() {
    // Test that multimethods dispatch based on hierarchy
    assert_eval_forms!(
        &[
            "(derive ::dog ::animal)",
            "(derive ::cat ::animal)",
            "(defmulti speak :type)",
            "(defmethod speak ::animal [_] \"generic sound\")",
            "(defmethod speak ::dog [_] \"woof\")",
            "(speak {:type ::dog})",
        ],
        KlujurVal::string("woof")
    );
}

#[test]
fn test_multimethod_hierarchy_fallback() {
    // When no exact match, should use parent's method
    assert_eval_forms!(
        &[
            "(derive ::cat ::animal)",
            "(defmulti speak :type)",
            "(defmethod speak ::animal [_] \"generic sound\")",
            "(speak {:type ::cat})",
        ],
        KlujurVal::string("generic sound")
    );
}

#[test]
fn test_underive_removes_relationship() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &["(def h (make-hierarchy))", "(derive h ::dog ::animal)"],
        &env,
    )
    .unwrap();

    // Before underive
    let result = eval_forms_with_env(&["(isa? h ::dog ::animal)"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(true));

    eval_forms_with_env(&["(underive h ::dog ::animal)"], &env).unwrap();

    // After underive
    let result = eval_forms_with_env(&["(isa? h ::dog ::animal)"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(false));
}

#[test]
fn test_derive_cyclic_error() {
    // Should error on cyclic derivation
    let result = eval_forms(&[
        "(def h (make-hierarchy))",
        "(derive h ::a ::b)",
        "(derive h ::b ::a)", // Would create cycle
    ]);
    assert!(result.is_err());
}

// =============================================================================
// prefer-method tests
// =============================================================================

#[test]
fn test_prefer_method_basic() {
    let env = Env::new();
    register_builtins(&env);

    // Create a hierarchy with multiple inheritance
    eval_forms_with_env(
        &[
            "(derive ::rect ::shape)",
            "(derive ::rect ::fillable)",
            "(defmulti draw :type)",
            "(defmethod draw ::shape [_] \"drawing shape\")",
            "(defmethod draw ::fillable [_] \"filling\")",
        ],
        &env,
    )
    .unwrap();

    // Without prefer-method, this would be ambiguous
    // Prefer ::shape over ::fillable
    eval_forms_with_env(&["(prefer-method draw ::shape ::fillable)"], &env).unwrap();

    // Now dispatch should use ::shape method
    let result = eval_forms_with_env(&["(draw {:type ::rect})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("drawing shape"));
}

#[test]
#[ignore] // TODO: prefers not implemented yet
fn test_prefer_method_with_prefers() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti f :type)",
            "(defmethod f ::a [_] :a)",
            "(defmethod f ::b [_] :b)",
            "(prefer-method f ::a ::b)",
        ],
        &env,
    )
    .unwrap();

    // prefers should return the preference map
    let result = eval_forms_with_env(&["(prefers f)"], &env).unwrap();
    // Should be a map with ::a -> #{::b}
    if let KlujurVal::Map(map, _) = result {
        assert!(!map.is_empty());
    } else {
        panic!("Expected map from prefers");
    }
}

// =============================================================================
// Custom hierarchy with multimethod
// =============================================================================

#[test]
#[ignore] // BUG: :hierarchy option expects hierarchy value directly, not var reference
fn test_multimethod_with_custom_hierarchy() {
    let env = Env::new();
    register_builtins(&env);

    // Create a custom hierarchy
    eval_forms_with_env(
        &[
            "(def my-h (make-hierarchy))",
            "(def my-h (derive my-h ::poodle ::dog))",
            "(def my-h (derive my-h ::dog ::animal))",
        ],
        &env,
    )
    .unwrap();

    // Create multimethod with custom hierarchy
    eval_forms_with_env(
        &[
            "(defmulti speak :type :hierarchy #'my-h)",
            "(defmethod speak ::animal [_] \"generic sound\")",
            "(defmethod speak ::dog [_] \"woof\")",
        ],
        &env,
    )
    .unwrap();

    // ::poodle should dispatch to ::dog (its parent in the custom hierarchy)
    let result = eval_forms_with_env(&["(speak {:type ::poodle})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("woof"));

    // ::dog should dispatch to ::dog directly
    let result = eval_forms_with_env(&["(speak {:type ::dog})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("woof"));
}

// =============================================================================
// Additional edge cases
// =============================================================================

#[test]
fn test_multimethod_redefine_method() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti greet :lang)",
            "(defmethod greet :en [_] \"Hello\")",
        ],
        &env,
    )
    .unwrap();

    // First call
    let result = eval_forms_with_env(&["(greet {:lang :en})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hello"));

    // Redefine the method
    eval_forms_with_env(&["(defmethod greet :en [_] \"Hi\")"], &env).unwrap();

    // Second call should use new implementation
    let result = eval_forms_with_env(&["(greet {:lang :en})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hi"));
}

#[test]
fn test_multimethod_no_method_error() {
    // Without a default method, missing dispatch value should error
    let result = eval_forms(&[
        "(defmulti process :type)",
        "(defmethod process :a [_] :a)",
        "(process {:type :unknown})", // No method for :unknown
    ]);
    assert!(result.is_err());
}

#[test]
fn test_get_method_with_hierarchy_fallback() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(derive ::child ::parent)",
            "(defmulti f :type)",
            "(defmethod f ::parent [_] \"parent\")",
        ],
        &env,
    )
    .unwrap();

    // get-method for ::child finds method through hierarchy
    // (this is actually correct Clojure behaviour)
    let result = eval_forms_with_env(&["(fn? (get-method f ::child))"], &env).unwrap();
    assert_eq!(result, KlujurVal::Bool(true));

    // Calling with ::child should work
    let result = eval_forms_with_env(&["(f {:type ::child})"], &env).unwrap();
    assert_eq!(result, KlujurVal::string("parent"));
}

#[test]
#[ignore] // TODO: remove-all-methods not implemented yet
fn test_remove_all_methods() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defmulti f identity)",
            "(defmethod f :a [_] :a)",
            "(defmethod f :b [_] :b)",
            "(defmethod f :default [_] :default)",
        ],
        &env,
    )
    .unwrap();

    // Verify methods exist
    let result = eval_forms_with_env(&["(count (methods f))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));

    // Remove all methods
    eval_forms_with_env(&["(remove-all-methods f)"], &env).unwrap();

    // Should have no methods
    let result = eval_forms_with_env(&["(count (methods f))"], &env).unwrap();
    assert_eq!(result, KlujurVal::int(0));
}

#[test]
fn test_multimethod_dispatch_on_nil() {
    assert_eval_forms!(
        &[
            "(defmulti f identity)",
            "(defmethod f nil [_] \"was nil\")",
            "(f nil)",
        ],
        KlujurVal::string("was nil")
    );
}

#[test]
fn test_multimethod_dispatch_on_false() {
    assert_eval_forms!(
        &[
            "(defmulti f identity)",
            "(defmethod f false [_] \"was false\")",
            "(f false)",
        ],
        KlujurVal::string("was false")
    );
}

#[test]
fn test_isa_with_class() {
    // isa? should work with nil
    assert_eval_forms!(&["(isa? nil nil)"], KlujurVal::Bool(true));
}

#[test]
fn test_multimethod_multiple_args() {
    // Dispatch function can use multiple arguments
    // Note: type returns string names like "int", "string"
    assert_eval_forms!(
        &[
            "(defmulti combine (fn [a b] [(type a) (type b)]))",
            "(defmethod combine [\"int\" \"int\"] [a b] (+ a b))",
            "(defmethod combine [\"string\" \"string\"] [a b] (str a b))",
            "(combine 1 2)",
        ],
        KlujurVal::int(3)
    );
}
