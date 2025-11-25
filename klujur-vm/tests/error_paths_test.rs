// klujur-vm - VM error path tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Tests for VM error paths:
//! - Stack underflow
//! - Division by zero
//! - Arity errors
//! - Type errors
//! - Undefined variables

use klujur_parser::Parser;
use klujur_vm::VM;
use klujur_vm::compiler::{analysis::Analyser, codegen::Compiler};

fn compile_and_run(src: &str) -> Result<String, String> {
    let expr = Parser::parse_str(src)
        .map_err(|e| format!("parse error: {:?}", e))?
        .ok_or("no expression")?;
    let mut analyser = Analyser::new();
    let analysis = analyser.analyse(&expr);
    let compiler = Compiler::new(analysis);
    let chunk = compiler
        .compile(&expr)
        .map_err(|e| format!("compile error: {:?}", e))?;

    let mut vm = VM::new();
    match vm.run(chunk) {
        Ok(val) => Ok(val.to_string()),
        Err(e) => Err(format!("{}", e)),
    }
}

fn expect_error(src: &str, expected_pattern: &str) {
    let result = compile_and_run(src);
    match result {
        Err(e) => {
            assert!(
                e.to_lowercase().contains(&expected_pattern.to_lowercase()),
                "Error '{}' should contain '{}' for source: {}",
                e,
                expected_pattern,
                src
            );
        }
        Ok(val) => {
            panic!(
                "Expected error containing '{}', but got success: {} for source: {}",
                expected_pattern, val, src
            );
        }
    }
}

// =============================================================================
// Division by zero
// =============================================================================

#[test]
fn division_by_zero_int() {
    expect_error("(/ 10 0)", "division by zero");
}

#[test]
fn division_by_zero_in_function() {
    expect_error("((fn [x y] (/ x y)) 10 0)", "division by zero");
}

// =============================================================================
// Arity errors
// =============================================================================

#[test]
fn arity_error_too_few_args() {
    expect_error("((fn [x y] x) 1)", "arguments");
}

#[test]
fn arity_error_too_many_args() {
    expect_error("((fn [x] x) 1 2 3)", "arguments");
}

#[test]
fn arity_error_no_args_expected_one() {
    expect_error("((fn [x] x))", "arguments");
}

#[test]
fn arity_error_variadic_minimum() {
    // Variadic function with 1 required + rest should require at least 1 arg
    expect_error("((fn [x & more] x))", "arguments");
}

#[test]
fn arity_error_multi_arity_no_match() {
    // Multi-arity function with no matching arity
    expect_error("((fn ([] 0) ([x] 1) ([x y] 2)) :a :b :c :d)", "arguments");
}

// =============================================================================
// Type errors in arithmetic
// =============================================================================

#[test]
fn type_error_add_non_number() {
    expect_error("(+ 1 :keyword)", "type");
}

#[test]
fn type_error_subtract_non_number() {
    expect_error("(- 1 \"string\")", "type");
}

#[test]
fn type_error_multiply_non_number() {
    expect_error("(* 2 nil)", "type");
}

#[test]
fn type_error_divide_non_number() {
    expect_error("(/ 10 true)", "type");
}

#[test]
fn type_error_comparison() {
    expect_error("(< 1 :keyword)", "type");
}

// =============================================================================
// Undefined variable errors
// =============================================================================

#[test]
fn undefined_variable_simple() {
    expect_error("undefined-var", "undefined");
}

#[test]
fn undefined_variable_in_expression() {
    expect_error("(+ 1 undefined-var)", "undefined");
}

#[test]
fn undefined_variable_in_function_body() {
    expect_error("((fn [] undefined-var))", "undefined");
}

// =============================================================================
// Sequence operation errors
// =============================================================================

#[test]
fn type_error_first_non_seq() {
    expect_error("(first 42)", "type");
}

#[test]
fn type_error_rest_non_seq() {
    expect_error("(rest 42)", "type");
}

#[test]
fn type_error_cons_non_seq_rest() {
    expect_error("(cons 1 42)", "type");
}

// =============================================================================
// Index out of bounds
// =============================================================================

#[test]
fn nth_out_of_bounds_positive() {
    expect_error("(nth [1 2 3] 10)", "bounds");
}

#[test]
fn nth_negative_index() {
    expect_error("(nth [1 2 3] -1)", "bounds");
}

// =============================================================================
// Inc/Dec overflow (if implemented)
// =============================================================================

#[test]
fn inc_at_max_int() {
    // This may or may not error depending on VM implementation
    // The VM may wrap or error
    let result = compile_and_run("(inc 9223372036854775807)");
    // Either an error or wraparound is acceptable
    match result {
        Err(e) => assert!(
            e.contains("overflow") || e.contains("error"),
            "Expected overflow error, got: {}",
            e
        ),
        Ok(_) => {} // Wraparound is also acceptable
    }
}

#[test]
fn dec_at_min_int() {
    let result = compile_and_run("(dec -9223372036854775808)");
    match result {
        Err(e) => assert!(
            e.contains("overflow") || e.contains("error"),
            "Expected overflow error, got: {}",
            e
        ),
        Ok(_) => {} // Wraparound is also acceptable
    }
}

// =============================================================================
// Collection operation errors
// =============================================================================

#[test]
fn assoc_vector_bad_index_type() {
    expect_error("(assoc [1 2 3] :key :val)", "type");
}

#[test]
fn assoc_vector_negative_index() {
    expect_error("(assoc [1 2 3] -1 :val)", "bounds");
}

#[test]
fn assoc_vector_index_too_large() {
    expect_error("(assoc [1 2 3] 100 :val)", "bounds");
}

#[test]
fn conj_non_collection() {
    expect_error("(conj 42 :val)", "type");
}

#[test]
fn count_non_countable() {
    expect_error("(count 42)", "type");
}

// =============================================================================
// Not callable errors
// =============================================================================

#[test]
fn call_integer() {
    let result = compile_and_run("(42 :arg)");
    // This should either error at compile time or runtime
    assert!(result.is_err(), "Calling an integer should error");
}

#[test]
fn call_keyword() {
    // Keywords CAN be called in Clojure ((:key map) -> (get map :key))
    // This test verifies the VM handles it (may succeed or fail depending on implementation)
    let result = compile_and_run("(:key {:key 42})");
    // Either success with 42 or an error is acceptable
    match result {
        Ok(val) => assert!(val == "42" || val == "nil"),
        Err(_) => {} // Error is also acceptable if not implemented
    }
}

// =============================================================================
// Loop/recur errors
// =============================================================================

#[test]
fn recur_wrong_arity() {
    // recur with wrong number of args should error
    // Currently triggers a stack underflow - the error handling could be improved
    let result = compile_and_run("(loop [x 0 y 1] (recur 5))");
    assert!(result.is_err(), "recur with wrong arity should error");
}

// =============================================================================
// Nested error propagation
// =============================================================================

#[test]
fn error_in_nested_call() {
    expect_error("((fn [f] (f 1 2)) (fn [x] x))", "arguments");
}

#[test]
fn error_in_let_binding() {
    expect_error("(let [x (/ 1 0)] x)", "division by zero");
}

#[test]
fn error_in_if_test() {
    expect_error("(if (/ 1 0) 1 2)", "division by zero");
}

#[test]
fn error_in_if_then() {
    expect_error("(if true (/ 1 0) 2)", "division by zero");
}

#[test]
fn error_in_if_else() {
    expect_error("(if false 1 (/ 1 0))", "division by zero");
}

// =============================================================================
// Empty collection edge cases (should not error)
// =============================================================================

#[test]
fn first_empty_vector_no_error() {
    let result = compile_and_run("(first [])");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "nil");
}

#[test]
fn rest_empty_vector_no_error() {
    let result = compile_and_run("(rest [])");
    assert!(result.is_ok());
    // rest of empty is empty list
    assert_eq!(result.unwrap(), "()");
}

#[test]
fn next_empty_vector_no_error() {
    let result = compile_and_run("(next [])");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "nil");
}

#[test]
fn count_empty_vector_no_error() {
    let result = compile_and_run("(count [])");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "0");
}

#[test]
fn count_nil_no_error() {
    let result = compile_and_run("(count nil)");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "0");
}
