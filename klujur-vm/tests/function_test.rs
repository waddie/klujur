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
    // Countdown loop using recur - now works with specialized opcodes for = and -
    assert_eq!(
        compile_and_run("(loop [n 5] (if (= n 0) n (recur (- n 1))))"),
        "0"
    );
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

// =============================================================================
// Transitive Closure Captures (grandparent+ scope)
// =============================================================================

#[test]
fn test_transitive_capture_two_levels() {
    // Capture from grandparent scope
    assert_eq!(compile_and_run("(let [x 42] ((fn [] ((fn [] x)))))"), "42");
}

#[test]
fn test_transitive_capture_three_levels() {
    // Capture from great-grandparent scope
    assert_eq!(
        compile_and_run("((((fn [a] (fn [b] (fn [c] a))) 1) 2) 3)"),
        "1"
    );
}

#[test]
fn test_transitive_capture_mixed_levels() {
    // Mix of direct and transitive captures
    assert_eq!(
        compile_and_run("(let [x 1] ((fn [y] ((fn [z] x) 3)) 2))"),
        "1"
    );
}

#[test]
fn test_transitive_capture_inner_shadows() {
    // Inner function shadows, should use nearest binding
    assert_eq!(
        compile_and_run("(let [x 1] ((fn [x] ((fn [] x))) 42))"),
        "42"
    );
}

// =============================================================================
// Multi-Arity Functions
// =============================================================================

#[test]
fn test_multi_arity_two_arities() {
    // Two fixed arities
    assert_eq!(compile_and_run("((fn ([x] x) ([x y] y)) 42)"), "42");
    assert_eq!(compile_and_run("((fn ([x] x) ([x y] y)) 1 2)"), "2");
}

#[test]
fn test_multi_arity_three_arities() {
    assert_eq!(compile_and_run("((fn ([] 0) ([x] 1) ([x y] 2)))"), "0");
    assert_eq!(compile_and_run("((fn ([] 0) ([x] 1) ([x y] 2)) :a)"), "1");
    assert_eq!(
        compile_and_run("((fn ([] 0) ([x] 1) ([x y] 2)) :a :b)"),
        "2"
    );
}

#[test]
fn test_multi_arity_with_body() {
    // Multi-arity with expressions in body
    assert_eq!(
        compile_and_run("((fn ([x] (+ x 1)) ([x y] (+ x y))) 10)"),
        "11"
    );
    assert_eq!(
        compile_and_run("((fn ([x] (+ x 1)) ([x y] (+ x y))) 10 20)"),
        "30"
    );
}

#[test]
fn test_multi_arity_with_variadic() {
    // Mix of fixed and variadic
    assert_eq!(compile_and_run("((fn ([x] x) ([x & more] more)) 42)"), "42");
    // Note: Variadic with extra args returns the rest list
    // This test would need list comparison which we don't have yet
}

#[test]
fn test_multi_arity_named() {
    // Named multi-arity function
    assert_eq!(
        compile_and_run("((fn foo ([x] x) ([x y] (+ x y))) 10)"),
        "10"
    );
    assert_eq!(
        compile_and_run("((fn foo ([x] x) ([x y] (+ x y))) 10 20)"),
        "30"
    );
}

// =============================================================================
// Mutable Captures (set! on captured variables)
// =============================================================================

#[test]
fn test_mutable_capture_simple() {
    // Closure that captures and mutates a variable
    assert_eq!(compile_and_run("(let [x 0] ((fn [] (set! x 42))) x)"), "42");
}

#[test]
fn test_mutable_capture_increment() {
    // Closure that increments a captured variable
    assert_eq!(
        compile_and_run("(let [x 0] ((fn [] (set! x (+ x 1)))) x)"),
        "1"
    );
}

#[test]
fn test_mutable_capture_multiple_calls() {
    // Call the same closure multiple times, mutating the captured variable
    assert_eq!(
        compile_and_run("(let [x 0 inc (fn [] (set! x (+ x 1)))] (inc) (inc) (inc) x)"),
        "3"
    );
}

#[test]
fn test_mutable_capture_read_and_write() {
    // Closure that both reads and writes to a captured variable
    assert_eq!(
        compile_and_run("(let [x 10] ((fn [] (let [old x] (set! x 20) old))))"),
        "10"
    );
}

#[test]
fn test_mutable_capture_two_closures() {
    // Two closures sharing the same mutable variable
    assert_eq!(
        compile_and_run("(let [x 0 inc (fn [] (set! x (+ x 1))) get (fn [] x)] (inc) (inc) (get))"),
        "2"
    );
}

#[test]
fn test_mutable_capture_nested() {
    // Nested function that mutates grandparent's variable
    assert_eq!(
        compile_and_run("(let [x 0] ((fn [] ((fn [] (set! x 99))))) x)"),
        "99"
    );
}

#[test]
fn test_mutable_capture_counter() {
    // Classic counter closure pattern
    assert_eq!(
        compile_and_run(
            "(let [count 0]
               (let [counter (fn [] (set! count (+ count 1)) count)]
                 (counter)
                 (counter)
                 (counter)))"
        ),
        "3"
    );
}
