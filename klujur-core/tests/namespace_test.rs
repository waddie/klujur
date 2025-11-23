// klujur-core - Namespace system integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur namespace system.
//!
//! Tests for: in-ns, require, use, alias, ns macro, helper functions

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{Keyword, KlujurVal, Parser, Symbol};
use std::fs;

/// Helper to evaluate a string and return the result.
fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).map_err(|e| e.to_string())?;
    eval_str_with_env(s, &env)
}

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    let mut result = KlujurVal::Nil;
    while let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
        result = eval(&expr, env).map_err(|e| e.to_string())?;
    }
    Ok(result)
}

/// Assert that evaluating `input` produces the expected value.
macro_rules! assert_eval {
    ($input:expr, $expected:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

/// Assert that evaluating `input` produces an error.
macro_rules! assert_eval_err {
    ($input:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
    };
}

/// Helper macro for tests with shared environment
macro_rules! assert_eval_eq_with_env {
    ($input:expr, $expected:expr, $env:expr) => {
        let result = eval_str_with_env($input, $env);
        assert!(
            result.is_ok(),
            "Failed to evaluate '{}': {:?}",
            $input,
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation of '{}' did not match expected",
            $input
        );
    };
}

// =============================================================================
// in-ns
// =============================================================================

#[test]
fn test_in_ns_basic() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Switch to new namespace
    assert_eval_eq_with_env!(
        "(in-ns 'test.core)",
        KlujurVal::symbol(Symbol::new("test.core")),
        &env
    );

    // Define a var in the new namespace
    eval_str_with_env("(def x 42)", &env).unwrap();

    // Switch back to user
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // x should not be visible in user namespace
    let result = eval_str_with_env("x", &env);
    assert!(result.is_err(), "x should not be visible in user namespace");
}

// =============================================================================
// all-ns, find-ns, create-ns, remove-ns, the-ns
// =============================================================================

#[test]
fn test_all_ns() {
    let result = eval_str("(all-ns)");
    assert!(result.is_ok());
    if let KlujurVal::List(items, _) = result.unwrap() {
        // Should at least contain 'user
        let names: Vec<String> = items
            .iter()
            .filter_map(|v| match v {
                KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"user".to_string()));
    } else {
        panic!("all-ns should return a list");
    }
}

#[test]
fn test_find_ns() {
    // User namespace should exist
    assert_eval!("(find-ns 'user)", KlujurVal::symbol(Symbol::new("user")));

    // Non-existent namespace returns nil
    assert_eval!("(find-ns 'nonexistent.ns)", KlujurVal::Nil);
}

#[test]
fn test_create_ns() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a new namespace
    assert_eval_eq_with_env!(
        "(create-ns 'my.new.ns)",
        KlujurVal::symbol(Symbol::new("my.new.ns")),
        &env
    );

    // Should now be findable
    assert_eval_eq_with_env!(
        "(find-ns 'my.new.ns)",
        KlujurVal::symbol(Symbol::new("my.new.ns")),
        &env
    );
}

#[test]
fn test_remove_ns() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace
    eval_str_with_env("(create-ns 'temp.ns)", &env).unwrap();

    // Remove it
    eval_str_with_env("(remove-ns 'temp.ns)", &env).unwrap();

    // Should no longer exist
    assert_eval_eq_with_env!("(find-ns 'temp.ns)", KlujurVal::Nil, &env);
}

#[test]
fn test_the_ns() {
    // User namespace should exist
    assert_eval!("(the-ns 'user)", KlujurVal::symbol(Symbol::new("user")));

    // Non-existent namespace should throw
    assert_eval_err!("(the-ns 'nonexistent.ns)");
}

// =============================================================================
// alias
// =============================================================================

#[test]
fn test_alias_basic() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with a var
    eval_str_with_env("(in-ns 'other.ns)", &env).unwrap();
    eval_str_with_env("(def x 42)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Create alias
    eval_str_with_env("(alias 'o 'other.ns)", &env).unwrap();

    // Access via alias
    assert_eval_eq_with_env!("o/x", KlujurVal::int(42), &env);
}

// =============================================================================
// refer
// =============================================================================

#[test]
fn test_refer_basic() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with a public var
    eval_str_with_env("(in-ns 'source.ns)", &env).unwrap();
    eval_str_with_env("(def public-fn (fn [x] (* x 2)))", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Refer the var
    eval_str_with_env("(refer 'source.ns)", &env).unwrap();

    // Should be accessible
    assert_eval_eq_with_env!("(public-fn 21)", KlujurVal::int(42), &env);
}

#[test]
fn test_refer_only() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create namespace with multiple vars
    eval_str_with_env("(in-ns 'source.ns)", &env).unwrap();
    eval_str_with_env("(def a 1)", &env).unwrap();
    eval_str_with_env("(def b 2)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Refer only 'a
    eval_str_with_env("(refer 'source.ns :only [a])", &env).unwrap();

    // a should be accessible, b should not
    assert_eval_eq_with_env!("a", KlujurVal::int(1), &env);
    assert!(eval_str_with_env("b", &env).is_err());
}

// =============================================================================
// load-file
// =============================================================================

#[test]
fn test_load_file() {
    // Create a temporary file
    let temp_dir = std::env::temp_dir();
    let test_file = temp_dir.join("klujur_test_load.klj");
    fs::write(&test_file, "(def loaded-value 123)").unwrap();

    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Load the file
    let load_cmd = format!("(load-file \"{}\")", test_file.display());
    eval_str_with_env(&load_cmd, &env).unwrap();

    // Check the var was defined
    assert_eval_eq_with_env!("loaded-value", KlujurVal::int(123), &env);

    // Clean up
    fs::remove_file(&test_file).ok();
}

// =============================================================================
// require with file loading
// =============================================================================

#[test]
fn test_require_with_file() {
    // Create temp directory structure
    let temp_dir = std::env::temp_dir().join("klujur_test_require");
    let lib_dir = temp_dir.join("mylib");
    fs::create_dir_all(&lib_dir).unwrap();

    // Create a test library file
    let utils_file = lib_dir.join("utils.klj");
    fs::write(
        &utils_file,
        r#"
(in-ns 'mylib.utils)
(def double (fn [x] (* 2 x)))
(def triple (fn [x] (* 3 x)))
"#,
    )
    .unwrap();

    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Add temp_dir to load paths
    env.registry().set_load_paths(vec![temp_dir.clone()]);

    // Require with alias
    eval_str_with_env("(require '[mylib.utils :as u])", &env).unwrap();

    // Use aliased function
    assert_eval_eq_with_env!("(u/double 21)", KlujurVal::int(42), &env);

    // Clean up
    fs::remove_dir_all(&temp_dir).ok();
}

#[test]
fn test_require_with_refer() {
    // Create temp directory structure
    let temp_dir = std::env::temp_dir().join("klujur_test_require_refer");
    let lib_dir = temp_dir.join("mylib");
    fs::create_dir_all(&lib_dir).unwrap();

    // Create a test library file
    let utils_file = lib_dir.join("utils.klj");
    fs::write(
        &utils_file,
        r#"
(in-ns 'mylib.utils)
(def double (fn [x] (* 2 x)))
(def triple (fn [x] (* 3 x)))
"#,
    )
    .unwrap();

    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Add temp_dir to load paths
    env.registry().set_load_paths(vec![temp_dir.clone()]);

    // Require with refer
    eval_str_with_env("(require '[mylib.utils :refer [double]])", &env).unwrap();

    // Use referred function directly
    assert_eval_eq_with_env!("(double 21)", KlujurVal::int(42), &env);

    // triple should not be directly accessible (not referred)
    assert!(eval_str_with_env("triple", &env).is_err());

    // But should be accessible via qualified name
    assert_eval_eq_with_env!("(mylib.utils/triple 14)", KlujurVal::int(42), &env);

    // Clean up
    fs::remove_dir_all(&temp_dir).ok();
}

// =============================================================================
// ns macro
// =============================================================================

#[test]
fn test_ns_macro_basic() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Use ns macro to switch namespace
    eval_str_with_env("(ns my.test.ns)", &env).unwrap();

    // Define something in the new namespace
    eval_str_with_env("(def x 99)", &env).unwrap();

    // Should be in my.test.ns
    assert_eval_eq_with_env!("x", KlujurVal::int(99), &env);
}

#[test]
fn test_ns_macro_with_require() {
    // Create temp directory structure
    let temp_dir = std::env::temp_dir().join("klujur_test_ns_require");
    let lib_dir = temp_dir.join("mylib");
    fs::create_dir_all(&lib_dir).unwrap();

    // Create a test library file
    let utils_file = lib_dir.join("utils.klj");
    fs::write(
        &utils_file,
        r#"
(in-ns 'mylib.utils)
(def double (fn [x] (* 2 x)))
"#,
    )
    .unwrap();

    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Add temp_dir to load paths
    env.registry().set_load_paths(vec![temp_dir.clone()]);

    // Use ns macro with require
    eval_str_with_env("(ns my.app (:require [mylib.utils :as u]))", &env).unwrap();

    // Use aliased function
    assert_eval_eq_with_env!("(u/double 21)", KlujurVal::int(42), &env);

    // Clean up
    fs::remove_dir_all(&temp_dir).ok();
}

// =============================================================================
// use
// =============================================================================

#[test]
fn test_use_basic() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with vars
    eval_str_with_env("(in-ns 'lib.math)", &env).unwrap();
    eval_str_with_env("(def add1 (fn [x] (+ x 1)))", &env).unwrap();
    eval_str_with_env("(def add2 (fn [x] (+ x 2)))", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Use the namespace - all vars should be available
    eval_str_with_env("(use 'lib.math)", &env).unwrap();

    assert_eval_eq_with_env!("(add1 10)", KlujurVal::int(11), &env);
    assert_eval_eq_with_env!("(add2 10)", KlujurVal::int(12), &env);
}

#[test]
fn test_use_with_only() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with vars
    eval_str_with_env("(in-ns 'lib.math)", &env).unwrap();
    eval_str_with_env("(def add1 (fn [x] (+ x 1)))", &env).unwrap();
    eval_str_with_env("(def add2 (fn [x] (+ x 2)))", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Use with :only filter
    eval_str_with_env("(use '[lib.math :only [add1]])", &env).unwrap();

    // add1 should be available
    assert_eval_eq_with_env!("(add1 10)", KlujurVal::int(11), &env);

    // add2 should NOT be available
    assert!(eval_str_with_env("add2", &env).is_err());
}

// =============================================================================
// require edge cases
// =============================================================================

#[test]
fn test_require_multiple_namespaces() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create two namespaces
    eval_str_with_env("(in-ns 'lib.a)", &env).unwrap();
    eval_str_with_env("(def a-val 1)", &env).unwrap();
    eval_str_with_env("(in-ns 'lib.b)", &env).unwrap();
    eval_str_with_env("(def b-val 2)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Require multiple namespaces
    eval_str_with_env("(require '[lib.a :as a] '[lib.b :as b])", &env).unwrap();

    assert_eval_eq_with_env!("a/a-val", KlujurVal::int(1), &env);
    assert_eval_eq_with_env!("b/b-val", KlujurVal::int(2), &env);
}

#[test]
fn test_require_refer_all() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with vars
    eval_str_with_env("(in-ns 'lib.util)", &env).unwrap();
    eval_str_with_env("(def x 1)", &env).unwrap();
    eval_str_with_env("(def y 2)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Require with :refer :all
    eval_str_with_env("(require '[lib.util :refer :all])", &env).unwrap();

    // All vars should be directly accessible
    assert_eval_eq_with_env!("x", KlujurVal::int(1), &env);
    assert_eval_eq_with_env!("y", KlujurVal::int(2), &env);
}

#[test]
fn test_require_nonexistent_error() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Requiring a namespace that doesn't exist should error
    let result = eval_str_with_env("(require 'nonexistent.namespace.xyz)", &env);
    assert!(result.is_err());
}

// =============================================================================
// ns macro advanced
// =============================================================================

#[test]
fn test_ns_macro_with_multiple_requires() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create two namespaces
    eval_str_with_env("(in-ns 'lib.a)", &env).unwrap();
    eval_str_with_env("(def a-fn (fn [] :a))", &env).unwrap();
    eval_str_with_env("(in-ns 'lib.b)", &env).unwrap();
    eval_str_with_env("(def b-fn (fn [] :b))", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Use ns macro with multiple requires
    eval_str_with_env(
        "(ns my.app
           (:require [lib.a :as a]
                     [lib.b :as b]))",
        &env,
    )
    .unwrap();

    assert_eval_eq_with_env!("(a/a-fn)", KlujurVal::keyword(Keyword::new("a")), &env);
    assert_eval_eq_with_env!("(b/b-fn)", KlujurVal::keyword(Keyword::new("b")), &env);
}

#[test]
fn test_ns_macro_with_use_clause() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace
    eval_str_with_env("(in-ns 'lib.core)", &env).unwrap();
    eval_str_with_env("(def core-fn (fn [] :core))", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Use ns macro with :use clause
    eval_str_with_env("(ns my.app (:use [lib.core :only [core-fn]]))", &env).unwrap();

    // core-fn should be directly accessible
    assert_eval_eq_with_env!("(core-fn)", KlujurVal::keyword(Keyword::new("core")), &env);
}

// =============================================================================
// ns-* functions
// =============================================================================

#[test]
fn test_ns_resolve() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Define a var
    eval_str_with_env("(def my-var 42)", &env).unwrap();

    // ns-resolve should return the var
    let result = eval_str_with_env("(ns-resolve 'user 'my-var)", &env);
    assert!(result.is_ok());
    // The result should be a var
    if let KlujurVal::Var(var) = result.unwrap() {
        assert_eq!(var.deref(), KlujurVal::int(42));
    } else {
        panic!("Expected var");
    }
}

#[test]
fn test_ns_resolve_nonexistent() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // ns-resolve for nonexistent var should return nil
    let result = eval_str_with_env("(ns-resolve 'user 'nonexistent-var)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn test_ns_resolve_qualified_symbol() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create a namespace with a var
    eval_str_with_env("(in-ns 'test.ns)", &env).unwrap();
    eval_str_with_env("(def foo 123)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // ns-resolve with qualified symbol should ignore the ns argument
    let result = eval_str_with_env("(ns-resolve 'user 'test.ns/foo)", &env);
    assert!(result.is_ok());
    if let KlujurVal::Var(var) = result.unwrap() {
        assert_eq!(var.deref(), KlujurVal::int(123));
    } else {
        panic!("Expected var");
    }
}

#[test]
fn test_ns_resolve_with_env_map() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Define a var
    eval_str_with_env("(def my-var 42)", &env).unwrap();

    // If symbol is in env map, should return nil (it's a local binding)
    let result = eval_str_with_env("(ns-resolve 'user {'my-var true} 'my-var)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);

    // If symbol is not in env map, should resolve normally
    let result = eval_str_with_env("(ns-resolve 'user {'other true} 'my-var)", &env);
    assert!(result.is_ok());
    if let KlujurVal::Var(var) = result.unwrap() {
        assert_eq!(var.deref(), KlujurVal::int(42));
    } else {
        panic!("Expected var");
    }
}

#[test]
fn test_ns_resolve_stdlib() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // ns-resolve should find vars defined by the stdlib
    // Note: Native builtins like + are in the lexical env, not interned as vars
    // The stdlib defines 'defn' as a macro in 'user' namespace
    let result = eval_str_with_env("(ns-resolve 'user 'defn)", &env);
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), KlujurVal::Var(_)));
}

#[test]
fn test_ns_resolve_nonexistent_namespace() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // ns-resolve for nonexistent namespace should return nil
    let result = eval_str_with_env("(ns-resolve 'nonexistent.ns 'foo)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn test_ns_name() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // ns-name should return the name of the namespace
    assert_eval_eq_with_env!(
        "(ns-name (the-ns 'user))",
        KlujurVal::symbol(Symbol::new("user")),
        &env
    );
}

#[test]
fn test_ns_publics() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create namespace with public vars
    eval_str_with_env("(in-ns 'test.ns)", &env).unwrap();
    eval_str_with_env("(def public-var 1)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // ns-publics should return a map
    let result = eval_str_with_env("(ns-publics 'test.ns)", &env);
    assert!(result.is_ok());
    if let KlujurVal::Map(map, _) = result.unwrap() {
        // Should contain public-var
        assert!(!map.is_empty());
    } else {
        panic!("Expected map");
    }
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_qualified_symbol_access() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Define a var in user namespace
    eval_str_with_env("(def my-val 123)", &env).unwrap();

    // Access via qualified symbol
    assert_eval_eq_with_env!("user/my-val", KlujurVal::int(123), &env);
}

#[test]
fn test_refer_exclude() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create namespace with multiple vars
    eval_str_with_env("(in-ns 'lib.all)", &env).unwrap();
    eval_str_with_env("(def keep-me 1)", &env).unwrap();
    eval_str_with_env("(def exclude-me 2)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Refer with :exclude
    eval_str_with_env("(refer 'lib.all :exclude [exclude-me])", &env).unwrap();

    // keep-me should be accessible
    assert_eval_eq_with_env!("keep-me", KlujurVal::int(1), &env);

    // exclude-me should NOT be accessible
    assert!(eval_str_with_env("exclude-me", &env).is_err());
}

#[test]
fn test_refer_rename() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Create namespace with a var
    eval_str_with_env("(in-ns 'lib.rename)", &env).unwrap();
    eval_str_with_env("(def orig-name 42)", &env).unwrap();
    eval_str_with_env("(in-ns 'user)", &env).unwrap();

    // Refer with :rename
    eval_str_with_env("(refer 'lib.rename :rename {orig-name new-name})", &env).unwrap();

    // Should be accessible via new name
    assert_eval_eq_with_env!("new-name", KlujurVal::int(42), &env);

    // Original name should NOT be accessible
    assert!(eval_str_with_env("orig-name", &env).is_err());
}
