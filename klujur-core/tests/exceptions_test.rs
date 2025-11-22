// klujur-core - Exception handling integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur exception handling.
//!
//! Tests for: try, throw, catch, finally, ex-info, ex-message, ex-data

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser};

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

// =============================================================================
// throw
// =============================================================================

#[test]
fn test_throw_simple() {
    assert_eval_err!("(throw \"error\")");
}

#[test]
fn test_throw_with_ex_info() {
    assert_eval_err!("(throw (ex-info \"oops\" {:code 404}))");
}

// =============================================================================
// try/catch
// =============================================================================

#[test]
fn test_try_without_exception() {
    assert_eval!("(try 42)", KlujurVal::int(42));
    assert_eval!("(try (+ 1 2))", KlujurVal::int(3));
}

#[test]
fn test_try_catch_default() {
    assert_eval!(
        "(try (throw \"error\") (catch :default e 42))",
        KlujurVal::int(42)
    );
}

#[test]
fn test_try_catch_throwable() {
    assert_eval!(
        "(try (throw \"error\") (catch Throwable e 42))",
        KlujurVal::int(42)
    );
}

#[test]
fn test_try_catch_exception() {
    assert_eval!(
        "(try (throw \"error\") (catch Exception e 42))",
        KlujurVal::int(42)
    );
}

#[test]
fn test_try_catch_binding() {
    // Catch should bind the thrown value
    assert_eval!(
        "(try (throw \"oops\") (catch :default e e))",
        KlujurVal::string("oops")
    );
}

#[test]
fn test_try_catch_with_ex_info() {
    // ex-message should extract message from ex-info map
    assert_eval!(
        "(try (throw (ex-info \"oops\" {:code 1})) (catch :default e (ex-message e)))",
        KlujurVal::string("oops")
    );
}

#[test]
fn test_try_catch_handler_body() {
    // Handler can have multiple expressions
    assert_eval!(
        "(try (throw \"err\") (catch :default e (+ 1 1) (+ 2 3)))",
        KlujurVal::int(5)
    );
}

#[test]
fn test_try_multiple_body_expressions() {
    // Try body can have multiple expressions
    assert_eval!("(try (+ 1 1) (+ 2 3))", KlujurVal::int(5));
}

#[test]
fn test_try_rethrow_uncaught() {
    // Exception without matching catch should propagate
    assert_eval_err!("(try (throw \"err\"))");
}

// =============================================================================
// finally
// =============================================================================

#[test]
fn test_try_finally_on_success() {
    // Finally runs but doesn't affect return value
    let env = Env::new();
    register_builtins(&env);

    // Use def to track if finally ran
    eval_str_with_env("(def ran-finally false)", &env).unwrap();
    let result = eval_str_with_env("(try 42 (finally (def ran-finally true)))", &env);
    assert_eq!(result.unwrap(), KlujurVal::int(42));

    // Check that finally ran
    let ran = eval_str_with_env("ran-finally", &env).unwrap();
    assert_eq!(ran, KlujurVal::bool(true));
}

#[test]
fn test_try_finally_on_exception() {
    // Finally runs even when exception is caught
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def ran-finally false)", &env).unwrap();
    let result = eval_str_with_env(
        "(try (throw \"err\") (catch :default e 42) (finally (def ran-finally true)))",
        &env,
    );
    assert_eq!(result.unwrap(), KlujurVal::int(42));

    let ran = eval_str_with_env("ran-finally", &env).unwrap();
    assert_eq!(ran, KlujurVal::bool(true));
}

#[test]
fn test_try_finally_on_uncaught() {
    // Finally runs even when exception is not caught
    let env = Env::new();
    register_builtins(&env);

    eval_str_with_env("(def ran-finally false)", &env).unwrap();
    let result = eval_str_with_env(
        "(try (throw \"err\") (finally (def ran-finally true)))",
        &env,
    );
    assert!(result.is_err());

    // Finally should still have run
    let ran = eval_str_with_env("ran-finally", &env).unwrap();
    assert_eq!(ran, KlujurVal::bool(true));
}

// =============================================================================
// ex-info, ex-message, ex-data
// =============================================================================

#[test]
fn test_ex_info_creates_map() {
    let result = eval_str("(ex-info \"message\" {:code 1})").unwrap();
    if let KlujurVal::Map(map, _) = result {
        let message_key = KlujurVal::Keyword(Keyword::new("message"));
        let data_key = KlujurVal::Keyword(Keyword::new("data"));

        assert_eq!(map.get(&message_key), Some(&KlujurVal::string("message")));
        assert!(map.get(&data_key).is_some());
    } else {
        panic!("ex-info should return a map");
    }
}

#[test]
fn test_ex_message() {
    assert_eval!(
        "(ex-message (ex-info \"oops\" {}))",
        KlujurVal::string("oops")
    );
}

#[test]
fn test_ex_message_on_string() {
    // ex-message on a plain string returns the string
    assert_eval!("(ex-message \"hello\")", KlujurVal::string("hello"));
}

#[test]
fn test_ex_data() {
    // ex-data extracts the :data key from an ex-info map
    let result = eval_str("(ex-data (ex-info \"msg\" {:code 42}))").unwrap();
    if let KlujurVal::Map(map, _) = result {
        let code_key = KlujurVal::Keyword(Keyword::new("code"));
        assert_eq!(map.get(&code_key), Some(&KlujurVal::int(42)));
    } else {
        panic!("ex-data should return the data map");
    }
}

#[test]
fn test_ex_data_on_non_map() {
    // ex-data on non-ex-info returns nil
    assert_eval!("(ex-data \"hello\")", KlujurVal::Nil);
}

// =============================================================================
// Catching internal errors
// =============================================================================

#[test]
fn test_catch_default_internal_error() {
    // :default should catch internal errors like arity errors
    // Use undefined symbol to trigger an error
    let result = eval_str("(try (undefined-symbol) (catch :default e :caught))");
    assert_eq!(result.unwrap(), KlujurVal::Keyword(Keyword::new("caught")));
}

#[test]
fn test_nested_try() {
    // Nested try blocks
    assert_eval!(
        "(try (try (throw \"inner\") (catch :default e :inner-caught)) (catch :default e :outer-caught))",
        KlujurVal::Keyword(Keyword::new("inner-caught"))
    );
}

#[test]
fn test_nested_try_rethrow() {
    // Inner try doesn't catch, outer does
    assert_eval!(
        "(try (try (throw \"err\")) (catch :default e :outer-caught))",
        KlujurVal::Keyword(Keyword::new("outer-caught"))
    );
}
