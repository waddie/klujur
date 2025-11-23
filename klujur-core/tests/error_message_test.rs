// klujur-core - Error message quality tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for error message quality.
//!
//! Tests that error messages are:
//! - Clear and understandable
//! - Consistent in format
//! - Include relevant context (e.g., function names, expected vs actual)
//! - Helpful for debugging

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{KlujurVal, Parser};

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

/// Assert that evaluation produces an error containing the specified substring.
macro_rules! assert_error_contains {
    ($input:expr, $expected:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.to_lowercase().contains(&$expected.to_lowercase()),
            "Error for '{}' should contain '{}', got: {}",
            $input,
            $expected,
            err_msg
        );
    };
}

// =============================================================================
// Undefined Symbol Errors
// =============================================================================

#[test]
fn test_undefined_symbol_error() {
    // Error should mention the undefined symbol
    assert_error_contains!("undefined-symbol", "undefined");
}

#[test]
fn test_undefined_symbol_includes_name() {
    // Error should include the symbol name for debugging
    assert_error_contains!("my-undefined-var", "my-undefined-var");
}

#[test]
fn test_undefined_in_expression() {
    // Should identify which symbol is undefined
    assert_error_contains!("(+ 1 unknown-value)", "unknown-value");
}

// =============================================================================
// Arity Errors
// =============================================================================

#[test]
fn test_arity_error_too_few_args() {
    // Error should indicate arity problem
    // Note: (+) returns 0 (identity), so use a function that requires args
    assert_error_contains!("(nth [1 2 3])", "argument");
}

#[test]
fn test_arity_error_mentions_function() {
    // Error should mention which function has the wrong arity
    let result = eval_str("(abs)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    // Should mention either the function name or arity
    assert!(
        err.contains("abs") || err.contains("arity") || err.contains("argument"),
        "Error should mention function or arity: {}",
        err
    );
}

#[test]
fn test_arity_error_expected_vs_got() {
    // Error should indicate expected vs actual arg count
    let result = eval_str("(if true)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("2") || err.contains("3") || err.contains("argument") || err.contains("arity"),
        "Error should mention expected args: {}",
        err
    );
}

// =============================================================================
// Type Errors
// =============================================================================

#[test]
fn test_type_error_mentions_expected() {
    // Error should say what type was expected
    let result = eval_str("(+ 1 \"string\")");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("number") || err.contains("integer") || err.contains("type"),
        "Error should mention expected type: {}",
        err
    );
}

#[test]
fn test_type_error_mentions_actual() {
    // Error should say what type was received
    let result = eval_str("(+ 1 :keyword)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("keyword") || err.contains("type"),
        "Error should mention actual type: {}",
        err
    );
}

#[test]
fn test_type_error_collection_ops() {
    // Collection operations should have clear type errors
    let result = eval_str("(first 42)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("seq")
            || err.contains("collection")
            || err.contains("type")
            || err.contains("argument"),
        "Error should mention sequence/collection: {}",
        err
    );
}

#[test]
fn test_type_error_string_ops() {
    // String operations should have clear type errors
    let result = eval_str("(subs 123 0 1)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("string") || err.contains("type"),
        "Error should mention string type: {}",
        err
    );
}

// =============================================================================
// Division and Arithmetic Errors
// =============================================================================

#[test]
fn test_division_by_zero_error() {
    assert_error_contains!("(/ 1 0)", "zero");
}

#[test]
fn test_mod_by_zero_error() {
    assert_error_contains!("(mod 10 0)", "zero");
}

#[test]
fn test_overflow_error_clear() {
    // Overflow errors should be clear
    assert_error_contains!("(+ 9223372036854775807 1)", "overflow");
}

// =============================================================================
// Collection Access Errors
// =============================================================================

#[test]
fn test_index_out_of_bounds() {
    // nth should give clear error for out of bounds
    let result = eval_str("(nth [1 2 3] 10)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("bound") || err.contains("index") || err.contains("range"),
        "Error should mention bounds/index: {}",
        err
    );
}

#[test]
fn test_negative_index_error() {
    let result = eval_str("(nth [1 2 3] -1)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("negative") || err.contains("index") || err.contains("bound"),
        "Error should mention negative index: {}",
        err
    );
}

// =============================================================================
// Special Form Errors
// =============================================================================

#[test]
fn test_let_binding_error() {
    // let with odd number of bindings
    let result = eval_str("(let* [x] x)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("binding") || err.contains("even") || err.contains("pair"),
        "Error should mention binding issue: {}",
        err
    );
}

#[test]
fn test_let_binding_not_vector() {
    let result = eval_str("(let* (x 1) x)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("vector") || err.contains("binding"),
        "Error should mention vector requirement: {}",
        err
    );
}

#[test]
fn test_fn_params_not_vector() {
    let result = eval_str("(fn* (x) x)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("vector") || err.contains("parameter"),
        "Error should mention vector parameters: {}",
        err
    );
}

#[test]
fn test_def_requires_symbol() {
    let result = eval_str("(def 123 :value)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("symbol"),
        "Error should mention symbol requirement: {}",
        err
    );
}

// =============================================================================
// Recur Errors
// =============================================================================

#[test]
fn test_recur_outside_loop() {
    // recur must be in loop or fn context
    let result = eval_str("(recur 1)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("recur")
            && (err.contains("loop") || err.contains("context") || err.contains("tail")),
        "Error should mention recur/loop context: {}",
        err
    );
}

#[test]
fn test_recur_wrong_arity() {
    // recur with wrong number of args
    let result = eval_str("(loop [x 1 y 2] (recur 10))");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("arity") || err.contains("argument") || err.contains("2") || err.contains("1"),
        "Error should mention arity mismatch: {}",
        err
    );
}

// =============================================================================
// Apply and Call Errors
// =============================================================================

#[test]
fn test_apply_non_function() {
    // Trying to call a non-function
    let result = eval_str("(42 1 2 3)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("call")
            || err.contains("function")
            || err.contains("apply")
            || err.contains("invoke"),
        "Error should mention function/call: {}",
        err
    );
}

#[test]
fn test_apply_nil() {
    let result = eval_str("(nil 1 2)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("nil") || err.contains("function") || err.contains("call"),
        "Error should mention nil/function: {}",
        err
    );
}

// =============================================================================
// Exception Errors
// =============================================================================

#[test]
fn test_throw_error_includes_message() {
    let result = eval_str("(throw (ex-info \"my custom error\" {:code 42}))");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("my custom error"),
        "Thrown error should include message: {}",
        err
    );
}

#[test]
fn test_throw_error_message_preserved() {
    // Simple string throw
    let result = eval_str("(throw \"simple error message\")");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("simple error message"),
        "Thrown string should be preserved: {}",
        err
    );
}

// =============================================================================
// Keyword Function Errors
// =============================================================================

#[test]
fn test_keyword_as_function_wrong_args() {
    // Keywords can be used as functions but need right arg count
    let result = eval_str("(:key)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("arity") || err.contains("argument") || err.contains("1") || err.contains("2"),
        "Error should mention arity: {}",
        err
    );
}

// =============================================================================
// Destructuring Errors
// =============================================================================

#[test]
fn test_destructure_non_sequential() {
    // Sequential destructuring on non-sequence
    let result = eval_str("(let* [[a b] 42] a)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("destruct")
            || err.contains("sequential")
            || err.contains("sequence")
            || err.contains("type"),
        "Error should mention destructuring issue: {}",
        err
    );
}

#[test]
fn test_destructure_map_non_associative() {
    // Map destructuring on non-map
    let result = eval_str("(let* [{:keys [a]} [1 2 3]] a)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("destruct")
            || err.contains("map")
            || err.contains("associative")
            || err.contains("type"),
        "Error should mention destructuring issue: {}",
        err
    );
}

// =============================================================================
// Reader/Parser Errors
// =============================================================================

#[test]
fn test_unmatched_paren() {
    let result = eval_str("(+ 1 2");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("unexpected")
            || err.contains("eof")
            || err.contains("paren")
            || err.contains("unmatched"),
        "Error should mention parsing issue: {}",
        err
    );
}

#[test]
fn test_unmatched_bracket() {
    let result = eval_str("[1 2 3");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("unexpected")
            || err.contains("eof")
            || err.contains("bracket")
            || err.contains("unmatched"),
        "Error should mention parsing issue: {}",
        err
    );
}

#[test]
fn test_invalid_number() {
    let result = eval_str("12.34.56");
    assert!(result.is_err());
    // Should fail to parse
}

// =============================================================================
// Multimethod Errors
// =============================================================================

#[test]
fn test_no_method_for_dispatch() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Define a multimethod but don't provide a method for the dispatch value
    eval_str_with_env("(defmulti greet :type)", &env).unwrap();
    eval_str_with_env("(defmethod greet :human [m] \"Hello, human!\")", &env).unwrap();

    // Try to dispatch on unhandled type
    let result = eval_str_with_env("(greet {:type :alien})", &env);
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("method") || err.contains("dispatch") || err.contains(":alien"),
        "Error should mention missing method: {}",
        err
    );
}

// =============================================================================
// Var and Namespace Errors
// =============================================================================

#[test]
fn test_var_not_found() {
    let result = eval_str("(var nonexistent-var)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("var") || err.contains("not found") || err.contains("nonexistent"),
        "Error should mention var not found: {}",
        err
    );
}

// =============================================================================
// Atom Errors
// =============================================================================

#[test]
fn test_swap_non_function() {
    let result = eval_str("(do (def a (atom 0)) (swap! a 42))");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("function") || err.contains("call") || err.contains("apply"),
        "Error should mention function requirement: {}",
        err
    );
}

#[test]
fn test_reset_non_atom() {
    let result = eval_str("(reset! 42 :value)");
    assert!(result.is_err());
    let err = result.unwrap_err().to_lowercase();
    assert!(
        err.contains("atom") || err.contains("type"),
        "Error should mention atom requirement: {}",
        err
    );
}

// =============================================================================
// Error Consistency Tests
// =============================================================================

#[test]
fn test_type_errors_consistent_format() {
    // Multiple type errors should have similar format
    let errors = vec![
        eval_str("(+ 1 :keyword)").unwrap_err(),
        eval_str("(+ 1 \"string\")").unwrap_err(),
        eval_str("(+ 1 [1 2 3])").unwrap_err(),
    ];

    // All should contain some type-related word
    for err in &errors {
        let err_lower = err.to_lowercase();
        assert!(
            err_lower.contains("type")
                || err_lower.contains("expected")
                || err_lower.contains("number"),
            "Type errors should have consistent format: {}",
            err
        );
    }
}

#[test]
fn test_arity_errors_consistent_format() {
    // Arity errors from different functions should be similar
    let errors = vec![
        eval_str("(inc)").unwrap_err(),
        eval_str("(dec)").unwrap_err(),
        eval_str("(abs)").unwrap_err(),
    ];

    // All should mention arity or arguments
    for err in &errors {
        let err_lower = err.to_lowercase();
        assert!(
            err_lower.contains("arity")
                || err_lower.contains("argument")
                || err_lower.contains("expected"),
            "Arity errors should have consistent format: {}",
            err
        );
    }
}
