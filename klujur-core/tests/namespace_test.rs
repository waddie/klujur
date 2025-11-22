// klujur-core - Namespace system integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur namespace system.
//!
//! Tests for: in-ns, require, use, alias, ns macro, helper functions

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{KlujurVal, Parser, Symbol};
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
