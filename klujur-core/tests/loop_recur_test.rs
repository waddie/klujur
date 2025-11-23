// klujur-core - Loop/recur integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur loop and recur special forms.
//!
//! Tests for: loop, recur, tail-call optimisation

mod common;

use common::{KlujurVal, eval_str_with_env, new_env};

// =============================================================================
// Basic loop/recur
// =============================================================================

#[test]
fn test_loop_basic() {
    // Simple loop that returns immediately
    assert_eval!("(loop [] 42)", KlujurVal::int(42));
}

#[test]
fn test_loop_single_binding() {
    assert_eval!("(loop [x 1] x)", KlujurVal::int(1));
}

#[test]
fn test_loop_multiple_bindings() {
    assert_eval!("(loop [x 1 y 2] (+ x y))", KlujurVal::int(3));
}

#[test]
fn test_loop_sequential_bindings() {
    // Loop bindings are sequential (like let*) - later bindings can reference earlier ones
    assert_eval!("(loop [x 1 y 2] (+ x y))", KlujurVal::int(3));
    assert_eval!("(loop [x 10 y (+ x 5)] y)", KlujurVal::int(15));
    assert_eval!("(loop [a 1 b (+ a 1) c (+ b 1)] c)", KlujurVal::int(3));
}

#[test]
fn test_loop_recur_count_down() {
    // Count down from 5 to 0
    assert_eval!(
        "(loop [n 5] (if (= n 0) :done (recur (- n 1))))",
        KlujurVal::keyword(common::Keyword::new("done"))
    );
}

#[test]
fn test_loop_recur_sum() {
    // Sum numbers from 1 to 10: 1+2+...+10 = 55
    assert_eval!(
        "(loop [n 10 sum 0] (if (= n 0) sum (recur (- n 1) (+ sum n))))",
        KlujurVal::int(55)
    );
}

#[test]
fn test_loop_recur_factorial() {
    // Factorial of 5 = 120
    assert_eval!(
        "(loop [n 5 acc 1] (if (<= n 1) acc (recur (- n 1) (* acc n))))",
        KlujurVal::int(120)
    );
}

#[test]
fn test_loop_recur_fibonacci() {
    // Fibonacci of 10 = 55
    assert_eval!(
        "(loop [n 10 a 0 b 1] (if (= n 0) a (recur (- n 1) b (+ a b))))",
        KlujurVal::int(55)
    );
}

// =============================================================================
// Recur in functions via loop
// =============================================================================

#[test]
fn test_fn_with_loop_recur() {
    // recur must be inside loop, even in a function body
    let env = new_env();
    eval_str_with_env(
        "(def countdown (fn* [n] (loop [x n] (if (= x 0) :done (recur (- x 1))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(countdown 5)", &env).unwrap();
    assert!(matches!(result, KlujurVal::Keyword(_)));
}

#[test]
fn test_fn_loop_recur_with_accumulator() {
    let env = new_env();
    eval_str_with_env(
        "(def sum-to (fn* [n] (loop [x n acc 0] (if (= x 0) acc (recur (- x 1) (+ acc x))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(sum-to 10)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(55));
}

#[test]
fn test_fn_loop_recur_factorial() {
    let env = new_env();
    eval_str_with_env(
        "(def fact (fn* [n] (loop [x n acc 1] (if (<= x 1) acc (recur (- x 1) (* acc x))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(fact 5)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(120));
}

#[test]
fn test_recur_in_fn_tail_position() {
    // recur directly in fn* (without loop) now works in tail position
    assert_eval!(
        "((fn* [n] (if (= n 0) :done (recur (- n 1)))) 5)",
        KlujurVal::keyword(common::Keyword::new("done"))
    );
}

#[test]
fn test_recur_in_fn_factorial() {
    // Factorial using recur in fn* tail position
    assert_eval!(
        "((fn* [n acc] (if (= n 0) acc (recur (- n 1) (* acc n)))) 5 1)",
        KlujurVal::int(120)
    );
}

#[test]
fn test_recur_in_fn_sum() {
    // Sum using recur in fn* tail position
    assert_eval!(
        "((fn* [n acc] (if (= n 0) acc (recur (- n 1) (+ acc n)))) 10 0)",
        KlujurVal::int(55)
    );
}

#[test]
fn test_recur_in_named_fn() {
    // Named function with recur
    let env = new_env();
    eval_str_with_env(
        "(def countdown (fn* countdown [n] (if (= n 0) :done (recur (- n 1)))))",
        &env,
    )
    .unwrap();
    let result = eval_str_with_env("(countdown 10)", &env).unwrap();
    assert_eq!(result, KlujurVal::keyword(common::Keyword::new("done")));
}

#[test]
fn test_recur_in_fn_wrong_arity() {
    // recur with wrong number of arguments should error
    assert_eval_err!("((fn* [n] (if (= n 0) :done (recur))) 5)");
    assert_eval_err!("((fn* [n] (if (= n 0) :done (recur 1 2))) 5)");
}

// =============================================================================
// Recur with collections
// =============================================================================

#[test]
fn test_loop_build_vector() {
    // Build a vector [1 2 3 4 5]
    assert_eval!(
        "(loop [n 5 v []] (if (= n 0) v (recur (- n 1) (conj v (- 6 n)))))",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5),
        ])
    );
}

#[test]
fn test_loop_process_list() {
    // Sum elements of a list
    let env = new_env();
    eval_str_with_env("(def xs '(1 2 3 4 5))", &env).unwrap();

    let result = eval_str_with_env(
        "(loop [items xs total 0]
           (if (empty? items)
             total
             (recur (rest items) (+ total (first items)))))",
        &env,
    )
    .unwrap();
    assert_eq!(result, KlujurVal::int(15));
}

#[test]
fn test_loop_reverse_list() {
    let env = new_env();
    eval_str_with_env("(def xs '(1 2 3))", &env).unwrap();

    let result = eval_str_with_env(
        "(loop [items xs acc '()]
           (if (empty? items)
             acc
             (recur (rest items) (cons (first items) acc))))",
        &env,
    )
    .unwrap();

    // Should be (3 2 1)
    assert_eq!(
        result,
        KlujurVal::list(vec![
            KlujurVal::int(3),
            KlujurVal::int(2),
            KlujurVal::int(1)
        ])
    );
}

// =============================================================================
// Nested loops
// =============================================================================

#[test]
fn test_nested_loops() {
    // Outer loop iterates 3 times, inner loop sums 1 to outer's value
    // Sum of (1) + (1+2) + (1+2+3) = 1 + 3 + 6 = 10
    assert_eval!(
        "(loop [i 3 total 0]
           (if (= i 0)
             total
             (recur (- i 1)
                    (+ total (loop [j i sum 0]
                               (if (= j 0)
                                 sum
                                 (recur (- j 1) (+ sum j))))))))",
        KlujurVal::int(10)
    );
}

// =============================================================================
// Recur with destructuring
// =============================================================================

#[test]
fn test_loop_with_vector_destructuring() {
    // Destructure a vector in loop bindings
    assert_eval!("(loop [[a b] [1 2]] (+ a b))", KlujurVal::int(3));
}

#[test]
fn test_loop_recur_with_destructuring() {
    // Process pairs, summing first elements
    let env = new_env();
    eval_str_with_env("(def pairs [[1 10] [2 20] [3 30]])", &env).unwrap();

    let result = eval_str_with_env(
        "(loop [ps pairs total 0]
           (if (empty? ps)
             total
             (let* [[a _] (first ps)]
               (recur (rest ps) (+ total a)))))",
        &env,
    )
    .unwrap();
    assert_eq!(result, KlujurVal::int(6)); // 1 + 2 + 3
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_loop_no_recur() {
    // Loop without recur just evaluates body once
    assert_eval!("(loop [x 1] (+ x 1))", KlujurVal::int(2));
}

#[test]
fn test_loop_immediate_return() {
    // Condition is immediately true
    assert_eval!(
        "(loop [n 0] (if (= n 0) :zero (recur (- n 1))))",
        KlujurVal::keyword(common::Keyword::new("zero"))
    );
}

#[test]
fn test_loop_empty_bindings() {
    // Loop with no bindings
    assert_eval!("(loop [] (+ 1 2))", KlujurVal::int(3));
}

#[test]
fn test_recur_updates_all_bindings() {
    // Verify all bindings are updated simultaneously
    // Swap x and y
    assert_eval!(
        "(loop [x 1 y 2 n 3]
           (if (= n 0)
             [x y]
             (recur y x (- n 1))))",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(1)])
    );
}

// =============================================================================
// Large iterations (stack safety)
// =============================================================================

#[test]
fn test_loop_large_iteration() {
    // Loop 1000 times - should not stack overflow due to TCO
    assert_eval!(
        "(loop [n 1000 sum 0] (if (= n 0) sum (recur (- n 1) (+ sum n))))",
        KlujurVal::int(500500) // Sum 1 to 1000
    );
}

#[test]
fn test_fn_large_iteration() {
    let env = new_env();
    // Must use loop for recur
    eval_str_with_env(
        "(def count-up (fn* [start limit] (loop [n start] (if (>= n limit) n (recur (+ n 1))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(count-up 0 1000)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(1000));
}

// =============================================================================
// Error cases
// =============================================================================

#[test]
fn test_recur_outside_loop_or_fn() {
    // recur outside of loop or fn should error
    assert_eval_err!("(recur 1)");
}

#[test]
fn test_recur_wrong_arity() {
    // Wrong number of args to recur
    assert_eval_err!("(loop [x 1 y 2] (recur 1))"); // Missing one arg
    assert_eval_err!("(loop [x 1] (recur 1 2))"); // Too many args
}

#[test]
fn test_recur_not_in_tail_position() {
    // recur must be in tail position - using it as an argument to a function should error
    assert_eval_err!("(loop [n 3] (if (= n 0) 0 (+ 1 (recur (- n 1)))))");
}

#[test]
fn test_recur_in_tail_position_of_if() {
    // recur IS in tail position when it's the result of an if branch
    // (the if itself is in tail position)
    assert_eval!(
        "(loop [n 5] (if (= n 0) :done (recur (- n 1))))",
        KlujurVal::keyword(common::Keyword::new("done"))
    );
}

// =============================================================================
// Interaction with other forms
// =============================================================================

#[test]
fn test_loop_with_let() {
    assert_eval!(
        "(loop [n 3 acc 0]
           (if (= n 0)
             acc
             (let* [doubled (* n 2)]
               (recur (- n 1) (+ acc doubled)))))",
        KlujurVal::int(12) // 6 + 4 + 2 = 12
    );
}

#[test]
fn test_loop_with_do() {
    let env = new_env();
    eval_str_with_env("(def counter (atom 0))", &env).unwrap();

    let result = eval_str_with_env(
        "(loop [n 5]
           (if (= n 0)
             @counter
             (do
               (swap! counter inc)
               (recur (- n 1)))))",
        &env,
    )
    .unwrap();
    assert_eq!(result, KlujurVal::int(5));
}

#[test]
fn test_loop_with_if_else() {
    // Test recur in both branches of if
    assert_eval!(
        "(loop [n 10 evens 0 odds 0]
           (if (= n 0)
             [evens odds]
             (if (= 0 (mod n 2))
               (recur (- n 1) (+ evens 1) odds)
               (recur (- n 1) evens (+ odds 1)))))",
        KlujurVal::vector(vec![KlujurVal::int(5), KlujurVal::int(5)])
    );
}

// =============================================================================
// Multiple body expressions
// =============================================================================

#[test]
fn test_loop_multiple_body_expressions() {
    // loop body should act like implicit do
    let env = new_env();
    eval_str_with_env("(def side-effect (atom 0))", &env).unwrap();

    let result = eval_str_with_env(
        "(loop [n 3]
           (swap! side-effect inc)
           (if (= n 0)
             @side-effect
             (recur (- n 1))))",
        &env,
    )
    .unwrap();
    // Side effect runs 4 times (n=3,2,1,0)
    assert_eq!(result, KlujurVal::int(4));
}
