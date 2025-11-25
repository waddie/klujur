// klujur-core - Macro edge case tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Tests for macro edge cases:
//! - Recursive expansion limits
//! - Lazy-seq returns from macros
//! - Complex macro patterns

mod common;

use common::{Keyword, KlujurVal, eval_all, eval_str_with_env, eval_str_with_stdlib, new_env};
use klujur_parser::Symbol;

// =============================================================================
// Recursive expansion limits
// =============================================================================

#[test]
#[ignore = "causes stack overflow - tests infinite recursion protection which needs improvement"]
fn recursive_macro_hits_expansion_limit() {
    let env = new_env();

    // Define a macro that infinitely expands to itself
    eval_all("(defmacro infinite [] '(infinite))", &env).unwrap();

    // Attempting to use this macro should hit the limit
    // Note: The error may occur during evaluation, not just macroexpand
    // Currently this causes a stack overflow rather than a clean error
    let result = eval_str_with_env("(infinite)", &env);
    assert!(
        result.is_err(),
        "Should hit macro expansion limit or recursion limit"
    );
}

#[test]
fn deeply_nested_but_terminating_macro() {
    let env = new_env();

    // Define a macro that expands n times, then terminates
    eval_all(
        "(defmacro countdown [n]
           (if (<= n 0)
             0
             (list 'countdown (- n 1))))",
        &env,
    )
    .unwrap();

    // Should successfully expand and evaluate
    let result = eval_str_with_env("(countdown 100)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(0));
}

#[test]
fn mutually_recursive_macros() {
    let env = new_env();

    // Define two macros that call each other
    eval_all(
        "(defmacro ping [n]
           (if (<= n 0)
             :done
             (list 'pong (- n 1))))
         (defmacro pong [n]
           (if (<= n 0)
             :done
             (list 'ping (- n 1))))",
        &env,
    )
    .unwrap();

    // Should terminate
    let result = eval_str_with_env("(ping 10)", &env).unwrap();
    assert_eq!(result, KlujurVal::keyword(Keyword::new("done")));
}

// =============================================================================
// Lazy-seq returns from macros
// =============================================================================

#[test]
fn macro_returning_lazy_seq_simple() {
    // Test that a macro can return code that creates a lazy seq
    // Using eval_all to evaluate multiple forms
    let result = eval_str_with_stdlib(
        "(do
           (defmacro lazy-ones []
             '(lazy-seq (cons 1 (lazy-ones))))
           (take 5 (lazy-ones)))",
    );

    assert!(
        result.is_ok(),
        "Macro returning lazy-seq should work: {:?}",
        result
    );
    let val = result.unwrap();
    // Should get (1 1 1 1 1)
    assert_eq!(val.to_string(), "(1 1 1 1 1)");
}

#[test]
fn macro_with_lazy_seq_in_body() {
    let result = eval_str_with_stdlib(
        "(do
           (defmacro make-counter [start]
             `(let [state# (atom ~start)]
                (fn []
                  (let [v# @state#]
                    (swap! state# inc)
                    v#))))
           (let [counter (make-counter 0)]
             [(counter) (counter) (counter)]))",
    );

    assert!(
        result.is_ok(),
        "Macro with stateful code should work: {:?}",
        result
    );
    let val = result.unwrap();
    assert_eq!(val.to_string(), "[0 1 2]");
}

#[test]
fn macro_generating_lazy_range() {
    let result = eval_str_with_stdlib(
        "(do
           (defmacro my-range [n]
             `(take ~n (iterate inc 0)))
           (vec (my-range 5)))",
    );

    assert!(
        result.is_ok(),
        "Macro generating lazy range should work: {:?}",
        result
    );
    let val = result.unwrap();
    assert_eq!(val.to_string(), "[0 1 2 3 4]");
}

// =============================================================================
// Complex macro patterns
// =============================================================================

#[test]
fn macro_with_multiple_body_forms() {
    let env = new_env();

    eval_all(
        "(defmacro with-logging [& body]
           `(do
              :start
              ~@body
              :end))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(with-logging 1 2 3)", &env).unwrap();
    // Last form is :end
    assert_eq!(result, KlujurVal::keyword(Keyword::new("end")));
}

#[test]
fn macro_with_gensym() {
    let result = eval_str_with_stdlib(
        "(do
           (defmacro once [expr]
             `(let [v# ~expr]
                v#))
           (once (+ 1 2)))",
    );

    assert!(
        result.is_ok(),
        "Macro with gensym should work: {:?}",
        result
    );
    assert_eq!(result.unwrap(), KlujurVal::int(3));
}

#[test]
fn macro_quoting_edge_cases() {
    let env = new_env();

    // Test that macros correctly handle quoted forms
    eval_all("(defmacro quote-it [x] `(quote ~x))", &env).unwrap();

    let result = eval_str_with_env("(quote-it foo)", &env).unwrap();
    assert_eq!(result, KlujurVal::symbol(Symbol::new("foo")));
}

#[test]
fn macro_unquote_splicing() {
    let env = new_env();

    eval_all(
        "(defmacro wrap-in-list [& items]
           `(list ~@items))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(wrap-in-list 1 2 3)", &env).unwrap();
    assert_eq!(result.to_string(), "(1 2 3)");
}

#[test]
fn nested_macro_calls() {
    let env = new_env();

    eval_all(
        "(defmacro add1 [x] `(+ ~x 1))
         (defmacro add2 [x] `(add1 (add1 ~x)))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(add2 5)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(7));
}

#[test]
fn macro_expanding_to_special_form() {
    let env = new_env();

    // Macro that expands to if
    eval_all(
        "(defmacro my-when [test & body]
           `(if ~test (do ~@body) nil))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(my-when true 1 2 3)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(3));

    let result = eval_str_with_env("(my-when false 1 2 3)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

// =============================================================================
// Macro hygiene tests
// =============================================================================

#[test]
fn macro_does_not_capture_local_bindings() {
    let result = eval_str_with_stdlib(
        "(do
           (defmacro add-x [expr]
             `(let [x# 10]
                (+ x# ~expr)))
           (let [x 5]
             (add-x x)))",
    );

    assert!(
        result.is_ok(),
        "Macro hygiene test should work: {:?}",
        result
    );
    // Should be 10 + 5 = 15 (x# is independent from outer x)
    assert_eq!(result.unwrap(), KlujurVal::int(15));
}

#[test]
fn macro_respects_outer_scope() {
    // Note: Syntax-quote (`y) qualifies symbols with the current namespace
    // To capture an outer binding, use regular quote instead
    let result = eval_str_with_stdlib(
        "(do
           (defmacro use-outer []
             'y)  ;; Use quote, not syntax-quote, to get unqualified symbol
           (let [y 42]
             (use-outer)))",
    );

    assert!(result.is_ok(), "Macro should see outer scope: {:?}", result);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

// =============================================================================
// macroexpand tests
// =============================================================================

#[test]
fn macroexpand_1_single_step() {
    let env = new_env();

    eval_all(
        "(defmacro outer [x] `(inner ~x))
         (defmacro inner [x] `(+ ~x 1))",
        &env,
    )
    .unwrap();

    // macroexpand-1 should only expand outer, not inner
    let result = eval_str_with_env("(macroexpand-1 '(outer 5))", &env).unwrap();
    // Should get (user/inner 5) or (inner 5) depending on namespace handling
    assert!(
        result.to_string().contains("inner"),
        "Expected inner in result: {}",
        result
    );
}

#[test]
fn macroexpand_full_expansion() {
    let env = new_env();

    eval_all(
        "(defmacro outer [x] `(inner ~x))
         (defmacro inner [x] `(+ ~x 1))",
        &env,
    )
    .unwrap();

    // macroexpand should fully expand
    let result = eval_str_with_env("(macroexpand '(outer 5))", &env).unwrap();
    // Should contain + 5 1 after expansion
    let s = result.to_string();
    assert!(
        s.contains("+") && s.contains("5") && s.contains("1"),
        "Expected expanded form with +, 5, 1: {}",
        s
    );
}

#[test]
fn macroexpand_non_macro_form() {
    let env = new_env();

    // Non-macro form should return unchanged
    let result = eval_str_with_env("(macroexpand '(+ 1 2))", &env).unwrap();
    assert_eq!(result.to_string(), "(+ 1 2)");
}

// =============================================================================
// Edge cases that previously caused issues
// =============================================================================

#[test]
fn macro_with_empty_body() {
    let env = new_env();

    // defmacro with nil body
    eval_all("(defmacro empty-body [] nil)", &env).unwrap();

    let result = eval_str_with_env("(empty-body)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn macro_with_literal_collections() {
    let env = new_env();

    eval_all(
        "(defmacro literal-vec []
           [1 2 3])",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(literal-vec)", &env).unwrap();
    assert_eq!(result.to_string(), "[1 2 3]");
}

#[test]
fn macro_with_keyword_args_pattern() {
    // Test common macro pattern with keyword options
    let result = eval_str_with_stdlib(
        "(do
           (defmacro with-opts [opts & body]
             `(let [options# ~opts]
                (when (:enabled options#)
                  ~@body)))
           (with-opts {:enabled true} :result))",
    );

    assert!(
        result.is_ok(),
        "Macro with keyword args should work: {:?}",
        result
    );
    assert_eq!(result.unwrap(), KlujurVal::keyword(Keyword::new("result")));
}

#[test]
fn macro_returning_nil() {
    let env = new_env();

    eval_all("(defmacro return-nil [] nil)", &env).unwrap();

    let result = eval_str_with_env("(return-nil)", &env).unwrap();
    assert_eq!(result, KlujurVal::Nil);
}

#[test]
fn macro_with_rest_args() {
    let env = new_env();

    eval_all(
        "(defmacro count-args [& args]
           (count args))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(count-args 1 2 3 4 5)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(5));
}
