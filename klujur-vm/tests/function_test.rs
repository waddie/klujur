// klujur-vm - Function call tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

use klujur_parser::Parser;
use klujur_vm::VM;
use klujur_vm::compiler::{analysis::Analyser, codegen::Compiler};

fn compile_and_run(src: &str) -> String {
    let expr = Parser::parse_str(src)
        .expect("parse error")
        .expect("no expression");
    let mut analyser = Analyser::new();
    let analysis = analyser.analyse(&expr);
    let compiler = Compiler::new(analysis);
    let chunk = compiler.compile(&expr).expect("compile error");

    let mut vm = VM::new();
    match vm.run(chunk) {
        Ok(val) => val.to_string(),
        Err(e) => format!("Error: {}", e),
    }
}

#[test]
fn test_literals() {
    assert_eq!(compile_and_run("42"), "42");
    assert_eq!(compile_and_run("3.14"), "3.14");
    assert_eq!(compile_and_run("true"), "true");
    assert_eq!(compile_and_run("false"), "false");
    assert_eq!(compile_and_run("nil"), "nil");
    assert_eq!(compile_and_run("\"hello\""), "\"hello\"");
    assert_eq!(compile_and_run(":keyword"), ":keyword");
}

#[test]
fn test_if() {
    assert_eq!(compile_and_run("(if true 1 2)"), "1");
    assert_eq!(compile_and_run("(if false 1 2)"), "2");
    assert_eq!(compile_and_run("(if nil 1 2)"), "2");
    assert_eq!(compile_and_run("(if 0 1 2)"), "1"); // 0 is truthy
}

#[test]
fn test_do() {
    assert_eq!(compile_and_run("(do 1 2 3)"), "3");
    assert_eq!(compile_and_run("(do)"), "nil");
    assert_eq!(compile_and_run("(do 42)"), "42");
}

#[test]
fn test_let() {
    assert_eq!(compile_and_run("(let [x 42] x)"), "42");
    assert_eq!(compile_and_run("(let [x 1 y 2] y)"), "2");
    assert_eq!(compile_and_run("(let [x 10 y 20] (if true x y))"), "10");
}

#[test]
fn test_def_and_globals() {
    assert_eq!(compile_and_run("(def x 42)"), "42");
    // Note: Can't test reading back globals yet since each run is independent
}

#[test]
fn test_fn_creation() {
    // Test that functions can be created (should return the function)
    let result = compile_and_run("(fn [] 42)");
    assert!(
        result.starts_with("#<fn"),
        "Expected function, got: {}",
        result
    );
}

#[test]
fn test_fn_call_no_args() {
    // Simple function with no arguments
    assert_eq!(compile_and_run("((fn [] 42))"), "42");
}

#[test]
fn test_fn_call_with_args() {
    // Function with arguments
    assert_eq!(compile_and_run("((fn [x] x) 42)"), "42");
    assert_eq!(compile_and_run("((fn [x y] x) 1 2)"), "1");
    assert_eq!(compile_and_run("((fn [x y] y) 1 2)"), "2");
}

#[test]
fn test_fn_nested_let() {
    assert_eq!(compile_and_run("((fn [x] (let [y 10] y)) 5)"), "10");
    assert_eq!(compile_and_run("((fn [x] (let [y 10] x)) 5)"), "5");
}

#[test]
fn test_fn_if_in_body() {
    assert_eq!(compile_and_run("((fn [x] (if x 1 0)) true)"), "1");
    assert_eq!(compile_and_run("((fn [x] (if x 1 0)) false)"), "0");
}

#[test]
fn test_named_fn_self_recursion_simple() {
    // A named function that just returns a value
    assert_eq!(compile_and_run("((fn fact [n] n) 5)"), "5");
}

#[test]
fn test_loop_recur_simple() {
    // Simple loop that immediately returns
    assert_eq!(compile_and_run("(loop [x 42] x)"), "42");
}

#[test]
fn test_quote() {
    assert_eq!(compile_and_run("(quote foo)"), "foo");
    assert_eq!(compile_and_run("(quote (1 2 3))"), "(1 2 3)");
}

#[test]
fn test_closure_simple() {
    // Simple closure capturing one variable
    assert_eq!(compile_and_run("(let [x 42] ((fn [] x)))"), "42");
}

#[test]
fn test_closure_multiple_captures() {
    // Closure capturing multiple variables
    assert_eq!(compile_and_run("(let [x 10 y 20] ((fn [] y)))"), "20");
    assert_eq!(compile_and_run("(let [x 10 y 20] ((fn [] x)))"), "10");
}

#[test]
fn test_closure_with_args() {
    // Closure capturing variable and taking argument
    assert_eq!(compile_and_run("(let [x 10] ((fn [y] y) 20))"), "20");
    assert_eq!(compile_and_run("(let [x 10] ((fn [y] x) 20))"), "10");
}

#[test]
fn test_closure_returned() {
    // Return a closure from a function
    assert_eq!(compile_and_run("(((fn [x] (fn [] x)) 42))"), "42");
}

#[test]
fn test_adder_closure() {
    // Classic make-adder example
    assert_eq!(compile_and_run("(((fn [n] (fn [x] n)) 10) 5)"), "10");
}

#[test]
fn test_loop_recur_countdown() {
    // Countdown loop using recur - requires builtins not yet available
    // For now, just verify the error message
    assert_eq!(
        compile_and_run("(loop [n 5] (if (= n 0) n (recur (- n 1))))"),
        "Error: Undefined variable: ="
    );
    // TODO: Need = and - builtins for this test to work properly
}

#[test]
fn test_loop_recur_accumulator() {
    // Simple accumulator pattern
    assert_eq!(compile_and_run("(loop [x 0] x)"), "0");
}

#[test]
fn test_nested_functions() {
    // Nested function calls
    assert_eq!(compile_and_run("((fn [x] ((fn [y] y) x)) 42)"), "42");
}

#[test]
fn test_higher_order_function() {
    // Apply a function to a value
    assert_eq!(compile_and_run("((fn [f x] (f x)) (fn [n] n) 99)"), "99");
}
