// klujur-core - Special forms integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur special forms.
//!
//! Tests for: if, do, let*, quote, fn*, def

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser, Symbol};

/// Helper to evaluate a string and return the result.
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
// if
// =============================================================================

#[test]
fn test_if_with_true_condition() {
    assert_eval!("(if true 1 2)", KlujurVal::int(1));
    assert_eval!("(if true 1)", KlujurVal::int(1));
}

#[test]
fn test_if_with_false_condition() {
    assert_eval!("(if false 1 2)", KlujurVal::int(2));
    assert_eval!("(if false 1)", KlujurVal::Nil);
}

#[test]
fn test_if_with_nil_condition() {
    assert_eval!("(if nil 1 2)", KlujurVal::int(2));
    assert_eval!("(if nil 1)", KlujurVal::Nil);
}

#[test]
fn test_if_truthiness() {
    // Everything except nil and false is truthy
    assert_eval!("(if 0 :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if -1 :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if 0.0 :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if \"\" :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if '() :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if [] :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if {} :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if #{} :t :f)", KlujurVal::keyword(Keyword::new("t")));
    assert_eval!("(if :keyword :t :f)", KlujurVal::keyword(Keyword::new("t")));
}

#[test]
fn test_if_nested() {
    assert_eval!(
        "(if true (if true :a :b) :c)",
        KlujurVal::keyword(Keyword::new("a"))
    );
    assert_eval!(
        "(if true (if false :a :b) :c)",
        KlujurVal::keyword(Keyword::new("b"))
    );
    assert_eval!(
        "(if false (if true :a :b) :c)",
        KlujurVal::keyword(Keyword::new("c"))
    );
}

#[test]
fn test_if_arity_errors() {
    assert_eval_err!("(if true)");
    assert_eval_err!("(if true 1 2 3)");
}

// =============================================================================
// do
// =============================================================================

#[test]
fn test_do_empty() {
    assert_eval!("(do)", KlujurVal::Nil);
}

#[test]
fn test_do_single_expression() {
    assert_eval!("(do 1)", KlujurVal::int(1));
}

#[test]
fn test_do_returns_last() {
    assert_eval!("(do 1 2 3)", KlujurVal::int(3));
}

#[test]
fn test_do_nested() {
    assert_eval!("(do (do 1) (do 2) 3)", KlujurVal::int(3));
}

#[test]
fn test_do_with_def() {
    assert_eval!("(do (def x 42) x)", KlujurVal::int(42));
}

#[test]
fn test_do_multiple_defs() {
    assert_eval!("(do (def a 1) (def b 2) (+ a b))", KlujurVal::int(3));
}

// =============================================================================
// let*
// =============================================================================

#[test]
fn test_let_empty() {
    assert_eval!("(let* [])", KlujurVal::Nil);
    assert_eval!("(let* [] 1)", KlujurVal::int(1));
}

#[test]
fn test_let_single_binding() {
    assert_eval!("(let* [x 1] x)", KlujurVal::int(1));
}

#[test]
fn test_let_multiple_bindings() {
    assert_eval!("(let* [x 1 y 2] (+ x y))", KlujurVal::int(3));
}

#[test]
fn test_let_sequential_binding() {
    assert_eval!("(let* [x 1 y (+ x 2)] y)", KlujurVal::int(3));
    assert_eval!(
        "(let* [a 1 b (+ a 1) c (+ b 1) d (+ c 1) e (+ d 1) f (+ e 1)] f)",
        KlujurVal::int(6)
    );
}

#[test]
fn test_let_shadowing() {
    assert_eval!("(let* [x 1] (let* [x 2] x))", KlujurVal::int(2));
}

#[test]
fn test_let_outer_binding_preserved() {
    // After inner let, outer x is still visible
    let env = Env::new();
    register_builtins(&env);

    // Evaluate multiple forms in same env
    let mut parser = Parser::new("(def result (let* [x 1] (let* [x 2] x) x))").unwrap();
    let expr = parser.parse().unwrap().unwrap();
    eval(&expr, &env).unwrap();

    let result = eval_str_with_env("result", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1));
}

#[test]
fn test_let_multiple_body_expressions() {
    assert_eval!("(let* [x 1] 1 2 3)", KlujurVal::int(3));
    assert_eval!(
        "(let* [x 1] :first :middle :last)",
        KlujurVal::keyword(Keyword::new("last"))
    );
}

#[test]
fn test_let_nested() {
    assert_eval!("(let* [x 1] (let* [y 2] (+ x y)))", KlujurVal::int(3));
    assert_eval!(
        "(let* [a 1] (let* [b 2] (let* [c 3] (+ a b c))))",
        KlujurVal::int(6)
    );
}

// =============================================================================
// quote
// =============================================================================

#[test]
fn test_quote_symbols() {
    assert_eval!("(quote foo)", KlujurVal::symbol(Symbol::new("foo")));
    assert_eval!("'foo", KlujurVal::symbol(Symbol::new("foo")));
}

#[test]
fn test_quote_numbers() {
    assert_eval!("(quote 42)", KlujurVal::int(42));
    assert_eval!("'42", KlujurVal::int(42));
}

#[test]
fn test_quote_strings() {
    assert_eval!("(quote \"hello\")", KlujurVal::string("hello"));
    assert_eval!("'\"hello\"", KlujurVal::string("hello"));
}

#[test]
fn test_quote_lists() {
    assert_eval!(
        "'(1 2 3)",
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
    // + is not called
    assert_eval!(
        "'(+ 1 2)",
        KlujurVal::list(vec![
            KlujurVal::symbol(Symbol::new("+")),
            KlujurVal::int(1),
            KlujurVal::int(2)
        ])
    );
}

#[test]
fn test_quote_vectors() {
    assert_eval!(
        "'[1 2 3]",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_quote_nested() {
    // ''x becomes (quote x)
    let result = eval_str("''x").unwrap();
    if let KlujurVal::List(items, _) = result {
        assert_eq!(items.len(), 2);
        assert_eq!(items[0], KlujurVal::symbol(Symbol::new("quote")));
        assert_eq!(items[1], KlujurVal::symbol(Symbol::new("x")));
    } else {
        panic!("Expected list");
    }
}

#[test]
fn test_quote_arity_errors() {
    assert_eval_err!("(quote)");
    assert_eval_err!("(quote a b)");
}

// =============================================================================
// fn*
// =============================================================================

#[test]
fn test_fn_creates_function() {
    let result = eval_str("(fn* [] 1)").unwrap();
    assert!(matches!(result, KlujurVal::Fn(_)));

    let result = eval_str("(fn* [x] x)").unwrap();
    assert!(matches!(result, KlujurVal::Fn(_)));
}

#[test]
fn test_fn_can_be_called() {
    assert_eval!("((fn* [] 1))", KlujurVal::int(1));
    assert_eval!("((fn* [x] x) 42)", KlujurVal::int(42));
}

#[test]
fn test_fn_single_parameter() {
    assert_eval!("((fn* [x] (+ x 1)) 1)", KlujurVal::int(2));
}

#[test]
fn test_fn_multiple_parameters() {
    assert_eval!("((fn* [x y z] (+ x y z)) 1 2 3)", KlujurVal::int(6));
}

#[test]
fn test_fn_multiple_body_expressions() {
    assert_eval!("((fn* [] 1 2 3))", KlujurVal::int(3));
}

#[test]
fn test_fn_rest_parameter() {
    // (fn* [& args] args) collects all args into a list
    let result = eval_str("((fn* [& args] args) 1 2 3)").unwrap();
    assert_eq!(
        result,
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_fn_mixed_and_rest_parameters() {
    // (fn* [a b & rest] ...) takes two required args then rest
    let result = eval_str("((fn* [a b & rest] rest) 1 2 3 4 5)").unwrap();
    assert_eq!(
        result,
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_fn_closure() {
    // Function captures outer environment
    assert_eval!("(let* [x 10] ((fn* [] x)))", KlujurVal::int(10));
}

#[test]
fn test_fn_arity_error() {
    // Calling with wrong number of args should error
    let result = eval_str("((fn* [x y] (+ x y)) 1)");
    assert!(result.is_err());

    let result = eval_str("((fn* [x] x) 1 2)");
    assert!(result.is_err());
}

// =============================================================================
// def
// =============================================================================

#[test]
fn test_def_creates_binding() {
    assert_eval!("(do (def x 42) x)", KlujurVal::int(42));
    assert_eval!(
        "(do (def my-var :value) my-var)",
        KlujurVal::keyword(Keyword::new("value"))
    );
}

#[test]
fn test_def_redefinition() {
    assert_eval!("(do (def x 1) (def x 2) x)", KlujurVal::int(2));
}

// =============================================================================
// Interaction between special forms
// =============================================================================

#[test]
fn test_if_inside_let() {
    assert_eval!(
        "(let* [x 1] (if (= x 1) :yes :no))",
        KlujurVal::keyword(Keyword::new("yes"))
    );
}

#[test]
fn test_let_inside_if() {
    assert_eval!("(if true (let* [x 42] x) 0)", KlujurVal::int(42));
}

#[test]
fn test_fn_inside_let() {
    assert_eval!("(let* [f (fn* [x] (+ x 1))] (f 2))", KlujurVal::int(3));
}

#[test]
fn test_let_inside_fn() {
    assert_eval!("((fn* [x] (let* [y 2] (+ x y))) 1)", KlujurVal::int(3));
}

#[test]
fn test_def_inside_do_inside_let() {
    assert_eval!(
        "(let* [result (do (def inner 42) inner)] result)",
        KlujurVal::int(42)
    );
}

#[test]
fn test_recursive_function() {
    // Test factorial using def for recursion
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env(
        "(def factorial (fn* [n] (if (<= n 1) 1 (* n (factorial (- n 1))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(factorial 5)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(120));
}

#[test]
fn test_mutually_recursive_functions() {
    let env = Env::new();
    register_builtins(&env);

    // even? and odd? defined mutually
    eval_str_with_env(
        "(def even? (fn* [n] (if (= n 0) true (odd? (- n 1)))))",
        &env,
    )
    .unwrap();
    eval_str_with_env(
        "(def odd? (fn* [n] (if (= n 0) false (even? (- n 1)))))",
        &env,
    )
    .unwrap();

    assert_eval_eq_with_env!("(even? 0)", KlujurVal::bool(true), &env);
    assert_eval_eq_with_env!("(even? 4)", KlujurVal::bool(true), &env);
    assert_eval_eq_with_env!("(odd? 3)", KlujurVal::bool(true), &env);
    assert_eval_eq_with_env!("(odd? 4)", KlujurVal::bool(false), &env);
}
