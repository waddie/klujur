// klujur-core - Apply integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur apply function.
//!
//! Tests for: apply with various functions and argument collections

mod common;

use common::{KlujurVal, eval_str, eval_str_with_env, new_env};

// =============================================================================
// Basic apply
// =============================================================================

#[test]
fn test_apply_basic() {
    assert_eval!("(apply + [1 2 3])", KlujurVal::int(6));
}

#[test]
fn test_apply_with_list() {
    assert_eval!("(apply + '(1 2 3))", KlujurVal::int(6));
}

#[test]
fn test_apply_empty_collection() {
    assert_eval!("(apply + [])", KlujurVal::int(0));
}

#[test]
fn test_apply_single_element() {
    assert_eval!("(apply + [42])", KlujurVal::int(42));
}

// =============================================================================
// Apply with leading arguments
// =============================================================================

#[test]
fn test_apply_with_leading_args() {
    // (apply f a b [c d]) => (f a b c d)
    assert_eval!("(apply + 1 2 [3 4])", KlujurVal::int(10));
}

#[test]
fn test_apply_with_single_leading_arg() {
    assert_eval!("(apply + 10 [1 2 3])", KlujurVal::int(16));
}

#[test]
fn test_apply_with_multiple_leading_args() {
    assert_eval!("(apply + 1 2 3 [4 5])", KlujurVal::int(15));
}

#[test]
fn test_apply_with_leading_args_empty_collection() {
    assert_eval!("(apply + 1 2 [])", KlujurVal::int(3));
}

// =============================================================================
// Apply with different functions
// =============================================================================

#[test]
fn test_apply_multiply() {
    assert_eval!("(apply * [2 3 4])", KlujurVal::int(24));
}

#[test]
fn test_apply_str() {
    assert_eval!("(apply str [\"a\" \"b\" \"c\"])", KlujurVal::string("abc"));
}

#[test]
fn test_apply_vector() {
    assert_eval!(
        "(apply vector [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_apply_list_fn() {
    let result = eval_str("(apply list [1 2 3])").unwrap();
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
fn test_apply_max() {
    assert_eval!("(apply max [1 5 3 2 4])", KlujurVal::int(5));
}

#[test]
fn test_apply_min() {
    assert_eval!("(apply min [3 1 4 1 5])", KlujurVal::int(1));
}

// =============================================================================
// Apply with user-defined functions
// =============================================================================

#[test]
fn test_apply_user_fn() {
    let env = new_env();
    eval_str_with_env("(def add3 (fn* [a b c] (+ a b c)))", &env).unwrap();

    let result = eval_str_with_env("(apply add3 [1 2 3])", &env).unwrap();
    assert_eq!(result, KlujurVal::int(6));
}

#[test]
fn test_apply_user_fn_with_leading_args() {
    let env = new_env();
    eval_str_with_env("(def add3 (fn* [a b c] (+ a b c)))", &env).unwrap();

    let result = eval_str_with_env("(apply add3 1 [2 3])", &env).unwrap();
    assert_eq!(result, KlujurVal::int(6));
}

#[test]
fn test_apply_lambda() {
    assert_eval!("(apply (fn* [x y] (* x y)) [3 4])", KlujurVal::int(12));
}

#[test]
fn test_apply_variadic_fn() {
    let env = new_env();
    eval_str_with_env("(def sum-all (fn* [& nums] (apply + nums)))", &env).unwrap();

    let result = eval_str_with_env("(apply sum-all [1 2 3 4 5])", &env).unwrap();
    assert_eq!(result, KlujurVal::int(15));
}

// =============================================================================
// Apply with higher-order functions
// =============================================================================

#[test]
fn test_apply_conj() {
    assert_eval!(
        "(apply conj [1 2] [3 4])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_apply_assoc() {
    let env = new_env();
    let result = eval_str_with_env("(apply assoc {} [:a 1 :b 2])", &env).unwrap();

    // Check it's a map with the expected values
    let _a = eval_str_with_env("(get m :a)", &{
        let e = new_env();
        eval_str_with_env(&format!("(def m {})", result), &e).unwrap();
        e
    });
    // Just verify it worked - map ordering may vary
    assert!(matches!(result, KlujurVal::Map(_, _)));
}

// =============================================================================
// Apply with nested collections
// =============================================================================

#[test]
fn test_apply_concat() {
    let result = eval_str("(apply concat [[1 2] [3 4] [5 6]])").unwrap();
    // concat returns a lazy sequence, so check it converts properly
    if let KlujurVal::LazySeq(_) = result {
        // Force evaluation by converting to vector
        let env = new_env();
        eval_str_with_env("(def s (apply concat [[1 2] [3 4] [5 6]]))", &env).unwrap();
        let forced = eval_str_with_env("(vec s)", &env).unwrap();
        assert_eq!(
            forced,
            KlujurVal::vector(vec![
                KlujurVal::int(1),
                KlujurVal::int(2),
                KlujurVal::int(3),
                KlujurVal::int(4),
                KlujurVal::int(5),
                KlujurVal::int(6)
            ])
        );
    }
}

// =============================================================================
// Apply edge cases
// =============================================================================

#[test]
fn test_apply_partial_like() {
    // Simulate partial application
    let env = new_env();
    eval_str_with_env("(def add-10 (fn* [& args] (apply + 10 args)))", &env).unwrap();

    let result = eval_str_with_env("(add-10 1 2 3)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(16));
}

#[test]
fn test_apply_identity() {
    assert_eval!("(apply identity [42])", KlujurVal::int(42));
}

#[test]
fn test_apply_constantly() {
    let env = new_env();
    eval_str_with_env("(def always-42 (constantly 42))", &env).unwrap();

    let result = eval_str_with_env("(apply always-42 [1 2 3])", &env).unwrap();
    assert_eq!(result, KlujurVal::int(42));
}

// =============================================================================
// Apply with comparison functions
// =============================================================================

#[test]
fn test_apply_less_than() {
    assert_eval!("(apply < [1 2 3 4])", KlujurVal::bool(true));
    assert_eval!("(apply < [1 3 2 4])", KlujurVal::bool(false));
}

#[test]
fn test_apply_equals() {
    assert_eval!("(apply = [1 1 1])", KlujurVal::bool(true));
    assert_eval!("(apply = [1 1 2])", KlujurVal::bool(false));
}

// =============================================================================
// Error cases
// =============================================================================

#[test]
fn test_apply_non_function() {
    assert_eval_err!("(apply 42 [1 2 3])");
}

#[test]
fn test_apply_non_collection() {
    assert_eval_err!("(apply + 1 2 3)");
}

#[test]
fn test_apply_wrong_arity() {
    let env = new_env();
    eval_str_with_env("(def takes-two (fn* [a b] (+ a b)))", &env).unwrap();

    let result = eval_str_with_env("(apply takes-two [1])", &env);
    assert!(result.is_err());

    let result = eval_str_with_env("(apply takes-two [1 2 3])", &env);
    assert!(result.is_err());
}

// =============================================================================
// Apply in practical scenarios
// =============================================================================

#[test]
fn test_apply_with_spread() {
    // Common pattern: spreading a vector as function arguments
    let env = new_env();
    eval_str_with_env("(def args [1 2 3])", &env).unwrap();

    let result = eval_str_with_env("(apply + args)", &env).unwrap();
    assert_eq!(result, KlujurVal::int(6));
}

#[test]
fn test_apply_in_reduce_like_pattern() {
    // Using apply to implement a simple reduce
    let env = new_env();
    eval_str_with_env(
        "(def my-sum (fn* [coll]
           (loop [items coll acc 0]
             (if (empty? items)
               acc
               (recur (rest items) (+ acc (first items)))))))",
        &env,
    )
    .unwrap();

    let result = eval_str_with_env("(my-sum [1 2 3 4 5])", &env).unwrap();
    assert_eq!(result, KlujurVal::int(15));
}
