// klujur-core - Dynamic binding integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur dynamic bindings.
//!
//! Tests for: binding, set!, dynamic vars, thread-bound?

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{KlujurVal, Parser};

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

// =============================================================================
// Dynamic var definition (earmuffs convention)
// =============================================================================

#[test]
fn test_earmuffed_var_is_dynamic() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    // The var should be dynamic
    let result = eval_str_with_env("(binding [*x* 2] *x*)", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(2));
}

#[test]
fn test_non_earmuffed_var_is_not_dynamic() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def x 1)", &env).unwrap();

    // Should error - can't bind non-dynamic var
    let result = eval_str_with_env("(binding [x 2] x)", &env);
    assert!(result.is_err());
}

// =============================================================================
// binding form
// =============================================================================

#[test]
fn test_binding_basic() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();
    let result = eval_str_with_env("(binding [*x* 42] *x*)", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_binding_restores_after_exit() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    // Inside binding, value is 42
    let result = eval_str_with_env("(binding [*x* 42] *x*)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));

    // Outside binding, value is back to 1
    let result = eval_str_with_env("*x*", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_binding_multiple_vars() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();
    eval_str_with_env("(def *y* 2)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 10 *y* 20] (+ *x* *y*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(30));
}

#[test]
fn test_binding_nested() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 10] (binding [*x* 100] *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(100));
}

#[test]
fn test_binding_nested_restores() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    // After inner binding exits, should restore to outer binding value
    let result = eval_str_with_env("(binding [*x* 10] (do (binding [*x* 100] *x*) *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(10));
}

// =============================================================================
// set!
// =============================================================================

#[test]
fn test_set_bang_within_binding() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 10] (do (set! *x* 42) *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_set_bang_outside_binding_fails() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    // Should error - can't set! outside binding context
    let result = eval_str_with_env("(set! *x* 42)", &env);
    assert!(result.is_err());
}

#[test]
fn test_set_bang_non_dynamic_fails() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def x 1)", &env).unwrap();

    // Should error - can't set! non-dynamic var
    let result = eval_str_with_env("(set! x 42)", &env);
    assert!(result.is_err());
}

#[test]
fn test_set_bang_does_not_affect_root() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    // set! inside binding doesn't change root
    eval_str_with_env("(binding [*x* 10] (set! *x* 42))", &env).unwrap();

    // Root value should still be 1
    let result = eval_str_with_env("*x*", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

// =============================================================================
// thread-bound?
// =============================================================================

#[test]
fn test_thread_bound_false_outside_binding() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(thread-bound? (var *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::bool(false));
}

#[test]
fn test_thread_bound_true_inside_binding() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 10] (thread-bound? (var *x*)))", &env);
    assert_eq!(result.unwrap(), KlujurVal::bool(true));
}

// =============================================================================
// var-get and var-set
// =============================================================================

#[test]
fn test_var_get_returns_root() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 42)", &env).unwrap();

    let result = eval_str_with_env("(var-get (var *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_var_get_returns_thread_binding() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 42] (var-get (var *x*)))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_var_set_within_binding() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env(
        "(binding [*x* 10] (do (var-set (var *x*) 42) (var-get (var *x*))))",
        &env,
    );
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

// =============================================================================
// bound?
// =============================================================================

#[test]
fn test_bound_true() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(bound? (var *x*))", &env);
    assert_eq!(result.unwrap(), KlujurVal::bool(true));
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_binding_with_function_call() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();
    eval_str_with_env("(def get-x (fn* [] *x*))", &env).unwrap();

    // Function should see the binding
    let result = eval_str_with_env("(binding [*x* 42] (get-x))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_binding_body_multiple_expressions() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def *x* 1)", &env).unwrap();

    let result = eval_str_with_env("(binding [*x* 10] (+ 1 1) (+ 2 2) *x*)", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(10));
}
