// klujur-core - Functions integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur functions.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser};

fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_str_with_env(s, &env)
}

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

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

// =============================================================================
// Basic fn*
// =============================================================================

#[test]
fn test_fn_creation() {
    let result = eval_str("(fn* [])").unwrap();
    assert!(matches!(result, KlujurVal::Fn(_)));

    let result = eval_str("(fn* [x] x)").unwrap();
    assert!(matches!(result, KlujurVal::Fn(_)));

    let result = eval_str("(fn* [x y] (+ x y))").unwrap();
    assert!(matches!(result, KlujurVal::Fn(_)));
}

#[test]
fn test_fn_invocation() {
    assert_eval!("((fn* []))", KlujurVal::Nil);
    assert_eval!("((fn* [] 42))", KlujurVal::int(42));
    assert_eval!("((fn* [x] x) 1)", KlujurVal::int(1));
    assert_eval!("((fn* [x y] (+ x y)) 1 2)", KlujurVal::int(3));
}

#[test]
fn test_fn_empty_params() {
    assert_eval!(
        "((fn* [] :value))",
        KlujurVal::keyword(Keyword::new("value"))
    );
    assert_eval!("(let* [f (fn* [] 42)] (f))", KlujurVal::int(42));
}

#[test]
fn test_fn_arity_errors() {
    assert_eval_err!("((fn* [x] x))"); // too few
    assert_eval_err!("((fn* [x] x) 1 2)"); // too many
}

// =============================================================================
// Rest Arguments (Variadic)
// =============================================================================

#[test]
fn test_fn_rest_args() {
    assert_eval!(
        "((fn* [& xs] xs) 1 2 3)",
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_fn_rest_args_empty() {
    // No rest args = nil (or empty list depending on implementation)
    let result = eval_str("((fn* [& xs] xs))").unwrap();
    // Could be nil or empty list - check both
    assert!(result == KlujurVal::Nil || result == KlujurVal::empty_list());
}

#[test]
fn test_fn_rest_args_with_required() {
    assert_eval!(
        "((fn* [a b & xs] xs) 1 2 3)",
        KlujurVal::list(vec![KlujurVal::int(3)])
    );
    assert_eval!(
        "((fn* [a b & xs] xs) 1 2 3 4 5)",
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_fn_rest_args_with_required_access() {
    assert_eval!("((fn* [a b & xs] a) 1 2 3 4 5)", KlujurVal::int(1));
    assert_eval!("((fn* [a b & xs] b) 1 2 3 4 5)", KlujurVal::int(2));
}

// =============================================================================
// Closures
// =============================================================================

#[test]
fn test_closure_basic() {
    assert_eval!("(let* [x 10] ((fn* [y] (+ x y)) 1))", KlujurVal::int(11));
    assert_eval!(
        "(let* [a 40] (let* [b 2] ((fn* [] (+ a b)))))",
        KlujurVal::int(42)
    );
}

#[test]
fn test_closure_nested() {
    assert_eval!(
        "(let* [x 1] (let* [y 2] (let* [z 3] ((fn* [] (+ x y z))))))",
        KlujurVal::int(6)
    );
}

#[test]
fn test_closure_returned() {
    // make-adder pattern
    assert_eval!(
        "(let* [make-adder (fn* [x] (fn* [y] (+ x y)))] ((make-adder 10) 1))",
        KlujurVal::int(11)
    );
    assert_eval!(
        "(let* [make-adder (fn* [x] (fn* [y] (+ x y))) add5 (make-adder 5)] (add5 10))",
        KlujurVal::int(15)
    );
}

#[test]
fn test_closure_shadows() {
    // Parameter shadows outer binding
    assert_eval!("(let* [x 10] ((fn* [x] x) 5))", KlujurVal::int(5));
    // But outer binding is preserved after call
    let env = Env::new();
    register_builtins(&env);
    eval_str_with_env("(def x 10)", &env).unwrap();
    eval_str_with_env("((fn* [x] x) 5)", &env).unwrap();
    let result = eval_str_with_env("x", &env).unwrap();
    assert_eq!(result, KlujurVal::int(10));
}

// =============================================================================
// Recursion via def
// =============================================================================

#[test]
fn test_recursive_factorial() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env(
        "(def fact (fn* [n] (if (<= n 1) 1 (* n (fact (- n 1))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(fact 5)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(120));

    let result = eval_str_with_env("(fact 0)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_recursive_fibonacci() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env(
        "(def fib (fn* [n] (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(fib 10)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(55));
}

// =============================================================================
// Function as First-Class Values
// =============================================================================

#[test]
fn test_fn_as_value() {
    // Store function in variable
    assert_eval!("(let* [f (fn* [x] (* x 2))] (f 5))", KlujurVal::int(10));
}

#[test]
fn test_fn_passed_as_argument() {
    // A function that applies its argument to 10
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def apply-to-10 (fn* [f] (f 10)))", &env).unwrap();

    let result = eval_str_with_env("(apply-to-10 (fn* [x] (* x 2)))", &env).unwrap();
    assert_eq!(result, KlujurVal::int(20));
}

// =============================================================================
// Native Functions
// =============================================================================

#[test]
fn test_native_fn_is_fn() {
    assert_eval!("(fn? +)", KlujurVal::bool(true));
    assert_eval!("(fn? -)", KlujurVal::bool(true));
    assert_eval!("(fn? first)", KlujurVal::bool(true));
}

#[test]
fn test_native_fn_can_be_passed() {
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def apply-to-pair (fn* [f a b] (f a b)))", &env).unwrap();

    let result = eval_str_with_env("(apply-to-pair + 3 4)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(7));

    let result = eval_str_with_env("(apply-to-pair * 3 4)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(12));
}

// =============================================================================
// identity
// =============================================================================

#[test]
fn test_identity_function() {
    assert_eval!("(identity 42)", KlujurVal::int(42));
    assert_eval!("(identity :x)", KlujurVal::keyword(Keyword::new("x")));
    assert_eval!(
        "(identity [1 2])",
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

// =============================================================================
// Multiple Body Expressions
// =============================================================================

#[test]
fn test_fn_multiple_body() {
    // fn* body is implicit do
    assert_eval!("((fn* [] 1 2 3))", KlujurVal::int(3));
    assert_eval!("((fn* [x] (def y (* x 2)) y) 5)", KlujurVal::int(10));
}
