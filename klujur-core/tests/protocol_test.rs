// klujur-core - Protocol integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur protocols.
//!
//! Tests for: defprotocol, extend-type, satisfies?, extends?, protocol dispatch

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
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

// =============================================================================
// Basic defprotocol
// =============================================================================

#[test]
fn test_defprotocol_creates_protocol() {
    let result = eval_forms(&["(defprotocol Greetable (greet [x]))", "(type Greetable)"]);
    assert_eq!(result.unwrap(), KlujurVal::string("protocol"));
}

#[test]
fn test_defprotocol_creates_method_var() {
    let result = eval_forms(&["(defprotocol Greetable (greet [x]))", "(fn? greet)"]);
    assert_eq!(result.unwrap(), KlujurVal::Bool(true));
}

#[test]
fn test_defprotocol_with_multiple_methods() {
    let result = eval_forms(&[
        "(defprotocol Describable
           (describe [x])
           (summarize [x n]))",
        "(fn? describe)",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::Bool(true));
}

// =============================================================================
// extend-type
// =============================================================================

#[test]
fn test_extend_type_string() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] (str \"Hello, \" s \"!\")))",
            "(greet \"world\")",
        ],
        KlujurVal::string("Hello, world!")
    );
}

#[test]
fn test_extend_type_vector() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]))",
            "(extend-type Vector
               Describable
               (describe [v] (str \"Vector with \" (count v) \" elements\")))",
            "(describe [1 2 3])",
        ],
        KlujurVal::string("Vector with 3 elements")
    );
}

#[test]
fn test_extend_type_multiple_methods() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable
               (describe [x])
               (summarize [x n]))",
            "(extend-type String
               Describable
               (describe [s] (str \"String: \" s))
               (summarize [s n] (subs s 0 (min n (count s)))))",
            "(describe \"hello\")",
        ],
        KlujurVal::string("String: hello")
    );
}

#[test]
fn test_extend_type_keyword() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type Keyword
               Greetable
               (greet [k] (str \"Greetings, \" (name k) \"!\")))",
            "(greet :friend)",
        ],
        KlujurVal::string("Greetings, friend!")
    );
}

#[test]
fn test_extend_type_integer() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type Int
               Greetable
               (greet [n] (str \"Number \" n \" says hi\")))",
            "(greet 42)",
        ],
        KlujurVal::string("Number 42 says hi")
    );
}

// =============================================================================
// satisfies?
// =============================================================================

#[test]
fn test_satisfies_true_for_extended_type() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] s))",
            "(satisfies? Greetable \"test\")",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_satisfies_false_for_unextended_type() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] s))",
            "(satisfies? Greetable 42)",
        ],
        KlujurVal::Bool(false)
    );
}

// =============================================================================
// extends?
// =============================================================================

#[test]
fn test_extends_true_for_extended_type() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] s))",
            "(extends? Greetable 'String)",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_extends_false_for_unextended_type() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] s))",
            "(extends? Greetable 'Int)",
        ],
        KlujurVal::Bool(false)
    );
}

// =============================================================================
// Protocol dispatch with multiple types
// =============================================================================

#[test]
fn test_protocol_dispatch_to_different_types() {
    let env = Env::new();
    register_builtins(&env);

    // Define protocol and extend to multiple types
    let setup_result = eval_forms_with_env(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend-type String
               Greetable
               (greet [s] (str \"Hello, \" s)))",
            "(extend-type Keyword
               Greetable
               (greet [k] (str \"Hi, \" (name k))))",
            "(extend-type Int
               Greetable
               (greet [n] (str \"Number \" n)))",
        ],
        &env,
    );
    assert!(setup_result.is_ok());

    // Test dispatch to String
    let string_result = eval_forms_with_env(&["(greet \"world\")"], &env);
    assert_eq!(string_result.unwrap(), KlujurVal::string("Hello, world"));

    // Test dispatch to Keyword
    let kw_result = eval_forms_with_env(&["(greet :friend)"], &env);
    assert_eq!(kw_result.unwrap(), KlujurVal::string("Hi, friend"));

    // Test dispatch to Int
    let int_result = eval_forms_with_env(&["(greet 42)"], &env);
    assert_eq!(int_result.unwrap(), KlujurVal::string("Number 42"));
}

// =============================================================================
// Error cases
// =============================================================================

#[test]
fn test_error_calling_unimplemented_protocol_method() {
    let result = eval_forms(&[
        "(defprotocol Greetable (greet [x]))",
        "(extend-type String
           Greetable
           (greet [s] s))",
        "(greet 42)",
    ]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No implementation"));
}

#[test]
fn test_error_extend_type_unknown_protocol() {
    let result = eval_forms(&["(extend-type String
           UnknownProtocol
           (method [s] s))"]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("Protocol not found"));
}

#[test]
fn test_error_extend_type_unknown_method() {
    let result = eval_forms(&[
        "(defprotocol Greetable (greet [x]))",
        "(extend-type String
           Greetable
           (unknown-method [s] s))",
    ]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("not part of protocol"));
}

// =============================================================================
// Protocol with method taking multiple arguments
// =============================================================================

#[test]
fn test_protocol_method_with_multiple_args() {
    assert_eval_forms!(
        &[
            "(defprotocol Combinable (combine [x y]))",
            "(extend-type String
               Combinable
               (combine [s1 s2] (str s1 s2)))",
            "(combine \"Hello, \" \"world!\")",
        ],
        KlujurVal::string("Hello, world!")
    );
}

#[test]
fn test_protocol_method_with_three_args() {
    assert_eval_forms!(
        &[
            "(defprotocol Calculator (calc [x y op]))",
            "(extend-type Int
               Calculator
               (calc [a b op]
                 (cond
                   (= op :add) (+ a b)
                   (= op :sub) (- a b)
                   (= op :mul) (* a b)
                   :else 0)))",
            "(calc 10 3 :add)",
        ],
        KlujurVal::int(13)
    );
}

// =============================================================================
// extend (low-level map-based extension)
// =============================================================================

#[test]
fn test_extend_with_keyword_method_map() {
    assert_eval_forms!(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(def greeting-fn (fn [s] (str \"Hello, \" s)))",
            "(extend String Greetable {:greet greeting-fn})",
            "(greet \"World\")",
        ],
        KlujurVal::string("Hello, World")
    );
}

#[test]
fn test_extend_with_anonymous_fn() {
    assert_eval_forms!(
        &[
            "(defprotocol Counter (count-it [x]))",
            "(extend Vector Counter {:count-it (fn [v] (count v))})",
            "(count-it [1 2 3])",
        ],
        KlujurVal::int(3)
    );
}

#[test]
fn test_extend_multiple_methods() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]) (summarize [x n]))",
            "(extend String
               Describable
               {:describe (fn [s] (str \"String: \" s))
                :summarize (fn [s n] (subs s 0 n))})",
            "(describe \"hello\")",
        ],
        KlujurVal::string("String: hello")
    );
}

#[test]
fn test_extend_works_with_dispatch() {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).unwrap();

    // Define protocol and extend using extend
    eval_forms_with_env(
        &[
            "(defprotocol Greetable (greet [x]))",
            "(extend String Greetable {:greet (fn [s] (str \"Str: \" s))})",
            "(extend Int Greetable {:greet (fn [n] (str \"Num: \" n))})",
        ],
        &env,
    )
    .unwrap();

    // Test dispatch to String
    let str_result = eval_forms_with_env(&["(greet \"test\")"], &env);
    assert_eq!(str_result.unwrap(), KlujurVal::string("Str: test"));

    // Test dispatch to Int
    let int_result = eval_forms_with_env(&["(greet 42)"], &env);
    assert_eq!(int_result.unwrap(), KlujurVal::string("Num: 42"));
}

#[test]
fn test_extend_error_unknown_method() {
    let result = eval_forms(&[
        "(defprotocol Greetable (greet [x]))",
        "(extend String Greetable {:unknown-method (fn [s] s)})",
    ]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("not part of protocol"));
}
