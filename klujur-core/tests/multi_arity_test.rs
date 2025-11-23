// klujur-core - Multi-arity defn tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for multi-arity function definitions via defn.
//!
//! Tests the `defn` macro with multiple parameter arities, including:
//! - Basic multi-arity dispatch
//! - Multi-arity with variadic (rest) parameters
//! - Multi-arity with docstrings and metadata
//! - Edge cases and error handling

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{KlujurVal, Parser};

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    let mut result = KlujurVal::Nil;
    while let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
        result = eval(&expr, env).map_err(|e| e.to_string())?;
    }
    Ok(result)
}

fn setup_env_with_stdlib() -> Env {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();
    env
}

// =============================================================================
// Basic Multi-Arity
// =============================================================================

#[test]
fn test_defn_multi_arity_basic() {
    let env = setup_env_with_stdlib();

    // Define a multi-arity function
    eval_str_with_env(
        "(defn greet
           ([] \"Hello\")
           ([name] (str \"Hello, \" name)))",
        &env,
    )
    .unwrap();

    // Call with no args
    let result = eval_str_with_env("(greet)", &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hello"));

    // Call with one arg
    let result = eval_str_with_env("(greet \"World\")", &env).unwrap();
    assert_eq!(result, KlujurVal::string("Hello, World"));
}

#[test]
fn test_defn_multi_arity_three_arities() {
    let env = setup_env_with_stdlib();

    // Define function with three arities
    eval_str_with_env(
        "(defn add-up
           ([] 0)
           ([a] a)
           ([a b] (+ a b))
           ([a b c] (+ a b c)))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(add-up)", &env).unwrap(),
        KlujurVal::int(0)
    );
    assert_eq!(
        eval_str_with_env("(add-up 5)", &env).unwrap(),
        KlujurVal::int(5)
    );
    assert_eq!(
        eval_str_with_env("(add-up 3 4)", &env).unwrap(),
        KlujurVal::int(7)
    );
    assert_eq!(
        eval_str_with_env("(add-up 1 2 3)", &env).unwrap(),
        KlujurVal::int(6)
    );
}

#[test]
fn test_defn_multi_arity_with_logic() {
    let env = setup_env_with_stdlib();

    // Multi-arity with different logic per arity
    eval_str_with_env(
        "(defn my-inc
           ([x] (+ x 1))
           ([x amount] (+ x amount)))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(my-inc 5)", &env).unwrap(),
        KlujurVal::int(6)
    );
    assert_eq!(
        eval_str_with_env("(my-inc 5 10)", &env).unwrap(),
        KlujurVal::int(15)
    );
}

// =============================================================================
// Multi-Arity with Rest Arguments
// =============================================================================

#[test]
fn test_defn_multi_arity_with_rest() {
    let env = setup_env_with_stdlib();

    // Multi-arity where one arity has rest args
    eval_str_with_env(
        "(defn variadic
           ([a] (list a))
           ([a b] (list a b))
           ([a b & more] (vec (concat (list a b) more))))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(variadic 1)", &env).unwrap(),
        KlujurVal::list(vec![KlujurVal::int(1)])
    );
    assert_eq!(
        eval_str_with_env("(variadic 1 2)", &env).unwrap(),
        KlujurVal::list(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
    // 3+ args should use the rest arity - use vec to realize the lazy seq
    let result = eval_str_with_env("(variadic 1 2 3 4)", &env).unwrap();
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_defn_rest_only_arity() {
    let env = setup_env_with_stdlib();

    // Function with only a rest parameter arity
    eval_str_with_env("(defn collect-all [& items] (vec items))", &env).unwrap();

    assert_eq!(
        eval_str_with_env("(collect-all)", &env).unwrap(),
        KlujurVal::empty_vector()
    );
    assert_eq!(
        eval_str_with_env("(collect-all 1 2 3)", &env).unwrap(),
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Multi-Arity with Docstring and Metadata
// =============================================================================

#[test]
fn test_defn_multi_arity_with_docstring() {
    let env = setup_env_with_stdlib();

    // Multi-arity with docstring
    eval_str_with_env(
        "(defn documented
           \"A function with documentation.\"
           ([] :zero)
           ([x] x))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(documented)", &env).unwrap().to_string(),
        ":zero"
    );
    assert_eq!(
        eval_str_with_env("(documented 42)", &env).unwrap(),
        KlujurVal::int(42)
    );
}

// =============================================================================
// Self-Recursion in Multi-Arity
// =============================================================================

#[test]
fn test_defn_multi_arity_self_recursion() {
    let env = setup_env_with_stdlib();

    // Factorial with multi-arity (common pattern)
    eval_str_with_env(
        "(defn factorial
           ([n] (factorial n 1))
           ([n acc]
            (if (<= n 1)
              acc
              (recur (dec n) (* n acc)))))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(factorial 0)", &env).unwrap(),
        KlujurVal::int(1)
    );
    assert_eq!(
        eval_str_with_env("(factorial 1)", &env).unwrap(),
        KlujurVal::int(1)
    );
    assert_eq!(
        eval_str_with_env("(factorial 5)", &env).unwrap(),
        KlujurVal::int(120)
    );
    assert_eq!(
        eval_str_with_env("(factorial 10)", &env).unwrap(),
        KlujurVal::int(3628800)
    );
}

#[test]
fn test_defn_multi_arity_mutual_calls() {
    let env = setup_env_with_stdlib();

    // One arity calling another
    eval_str_with_env(
        "(defn range-sum
           ([n] (range-sum 0 n 0))
           ([start end] (range-sum start end 0))
           ([start end acc]
            (if (>= start end)
              acc
              (recur (inc start) end (+ acc start)))))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(range-sum 5)", &env).unwrap(),
        KlujurVal::int(10) // 0+1+2+3+4
    );
    assert_eq!(
        eval_str_with_env("(range-sum 1 5)", &env).unwrap(),
        KlujurVal::int(10) // 1+2+3+4
    );
}

// =============================================================================
// Arity Errors
// =============================================================================

#[test]
fn test_defn_multi_arity_wrong_arity() {
    let env = setup_env_with_stdlib();

    // Define function with specific arities
    eval_str_with_env(
        "(defn fixed-arities
           ([] :zero)
           ([x] :one)
           ([x y] :two))",
        &env,
    )
    .unwrap();

    // Calling with wrong arity should error
    let result = eval_str_with_env("(fixed-arities 1 2 3)", &env);
    assert!(result.is_err(), "Expected arity error for 3 args");
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_defn_single_arity_still_works() {
    // Ensure single-arity defn still works (not multi-arity form)
    let env = setup_env_with_stdlib();

    eval_str_with_env("(defn single [x y] (+ x y))", &env).unwrap();

    assert_eq!(
        eval_str_with_env("(single 3 4)", &env).unwrap(),
        KlujurVal::int(7)
    );
}

#[test]
fn test_defn_multi_arity_preserves_closures() {
    let env = setup_env_with_stdlib();

    // Define a function that returns a multi-arity closure
    eval_str_with_env(
        "(defn make-adder [base]
           (fn
             ([] base)
             ([x] (+ base x))
             ([x y] (+ base x y))))",
        &env,
    )
    .unwrap();

    eval_str_with_env("(def add10 (make-adder 10))", &env).unwrap();

    assert_eq!(
        eval_str_with_env("(add10)", &env).unwrap(),
        KlujurVal::int(10)
    );
    assert_eq!(
        eval_str_with_env("(add10 5)", &env).unwrap(),
        KlujurVal::int(15)
    );
    assert_eq!(
        eval_str_with_env("(add10 5 3)", &env).unwrap(),
        KlujurVal::int(18)
    );
}

#[test]
fn test_defn_multi_arity_all_empty_body() {
    let env = setup_env_with_stdlib();

    // Arities that return nil
    eval_str_with_env(
        "(defn do-nothing
           ([])
           ([_]))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(do-nothing)", &env).unwrap(),
        KlujurVal::Nil
    );
    assert_eq!(
        eval_str_with_env("(do-nothing :ignored)", &env).unwrap(),
        KlujurVal::Nil
    );
}

#[test]
fn test_defn_multi_arity_destructuring() {
    let env = setup_env_with_stdlib();

    // Multi-arity with destructuring
    eval_str_with_env(
        "(defn extract
           ([[a b]] (+ a b))
           ([[a b] [c d]] (+ a b c d)))",
        &env,
    )
    .unwrap();

    assert_eq!(
        eval_str_with_env("(extract [1 2])", &env).unwrap(),
        KlujurVal::int(3)
    );
    assert_eq!(
        eval_str_with_env("(extract [1 2] [3 4])", &env).unwrap(),
        KlujurVal::int(10)
    );
}
