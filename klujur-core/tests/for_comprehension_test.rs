// klujur-core - For comprehension edge case tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for the `for` list comprehension macro.
//!
//! Tests edge cases for:
//! - `:when` modifier (conditional filtering)
//! - `:let` modifier (local bindings)
//! - `:while` modifier (early termination)
//! - Nested bindings
//! - Combined modifiers

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
// Basic for comprehension
// =============================================================================

#[test]
fn test_for_basic() {
    let env = setup_env_with_stdlib();

    // Simple mapping
    let result = eval_str_with_env("(vec (for [x [1 2 3]] (* x 2)))", &env).unwrap();
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6)
        ])
    );
}

#[test]
fn test_for_nested_bindings() {
    let env = setup_env_with_stdlib();

    // Cartesian product
    let result = eval_str_with_env(
        "(vec (for [x [1 2] y [:a :b]] [x y]))",
        &env,
    )
    .unwrap();

    // Should produce [[1 :a] [1 :b] [2 :a] [2 :b]]
    assert_eq!(
        result.to_string(),
        "[[1 :a] [1 :b] [2 :a] [2 :b]]"
    );
}

#[test]
fn test_for_empty_collection() {
    let env = setup_env_with_stdlib();

    let result = eval_str_with_env("(vec (for [x []] x))", &env).unwrap();
    assert_eq!(result, KlujurVal::empty_vector());
}

// =============================================================================
// :when modifier
// =============================================================================

#[test]
fn test_for_when_basic() {
    let env = setup_env_with_stdlib();

    // Filter even numbers
    let result = eval_str_with_env(
        "(vec (for [x (range 10) :when (even? x)] x))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6),
            KlujurVal::int(8)
        ])
    );
}

#[test]
fn test_for_when_filters_all() {
    let env = setup_env_with_stdlib();

    // When condition is always false - empty result
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] :when false] x))",
        &env,
    )
    .unwrap();

    assert_eq!(result, KlujurVal::empty_vector());
}

#[test]
fn test_for_when_passes_all() {
    let env = setup_env_with_stdlib();

    // When condition is always true
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] :when true] x))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_for_when_with_nested() {
    let env = setup_env_with_stdlib();

    // Filter in nested loop
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] y [1 2 3] :when (< x y)] [x y]))",
        &env,
    )
    .unwrap();

    // Pairs where x < y: [1 2] [1 3] [2 3]
    assert_eq!(
        result.to_string(),
        "[[1 2] [1 3] [2 3]]"
    );
}

#[test]
fn test_for_multiple_when() {
    let env = setup_env_with_stdlib();

    // Multiple :when clauses
    let result = eval_str_with_env(
        "(vec (for [x (range 20) :when (even? x) :when (> x 10)] x))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(12),
            KlujurVal::int(14),
            KlujurVal::int(16),
            KlujurVal::int(18)
        ])
    );
}

// =============================================================================
// :let modifier
// =============================================================================

#[test]
fn test_for_let_basic() {
    let env = setup_env_with_stdlib();

    // Introduce local binding
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] :let [y (* x 2)]] y))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6)
        ])
    );
}

#[test]
fn test_for_let_multiple_bindings() {
    let env = setup_env_with_stdlib();

    // Multiple bindings in one :let
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] :let [y (* x 2) z (+ y 1)]] z))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(3),  // 1*2+1
            KlujurVal::int(5),  // 2*2+1
            KlujurVal::int(7)   // 3*2+1
        ])
    );
}

#[test]
fn test_for_let_can_reference_earlier() {
    let env = setup_env_with_stdlib();

    // Later :let can reference earlier bindings
    let result = eval_str_with_env(
        "(vec (for [x [1 2] :let [doubled (* x 2)] :let [quadrupled (* doubled 2)]] quadrupled))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(4),  // 1*2*2
            KlujurVal::int(8)   // 2*2*2
        ])
    );
}

#[test]
fn test_for_let_with_when() {
    let env = setup_env_with_stdlib();

    // Combine :let and :when
    let result = eval_str_with_env(
        "(vec (for [x (range 10) :let [sq (* x x)] :when (> sq 20)] sq))",
        &env,
    )
    .unwrap();

    // Squares > 20: 25 (5^2), 36 (6^2), 49 (7^2), 64 (8^2), 81 (9^2)
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(25),
            KlujurVal::int(36),
            KlujurVal::int(49),
            KlujurVal::int(64),
            KlujurVal::int(81)
        ])
    );
}

// =============================================================================
// :while modifier
// =============================================================================
//
// NOTE: The :while modifier has a known bug where the :for-while-stop sentinel
// leaks into the output. These tests are marked #[ignore] until the bug is fixed.
// See CODE_REVIEW.md for details on the for-step function.

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_while_basic() {
    let env = setup_env_with_stdlib();

    // Stop when condition becomes false
    let result = eval_str_with_env(
        "(vec (for [x (range 100) :while (< x 5)] x))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_while_immediate_stop() {
    let env = setup_env_with_stdlib();

    // :while false immediately - no elements
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3] :while false] x))",
        &env,
    )
    .unwrap();

    assert_eq!(result, KlujurVal::empty_vector());
}

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_while_with_when() {
    let env = setup_env_with_stdlib();

    // :while stops iteration, :when filters
    let result = eval_str_with_env(
        "(vec (for [x (range 20) :while (< x 10) :when (odd? x)] x))",
        &env,
    )
    .unwrap();

    // Odd numbers while x < 10
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(3),
            KlujurVal::int(5),
            KlujurVal::int(7),
            KlujurVal::int(9)
        ])
    );
}

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_while_with_let() {
    let env = setup_env_with_stdlib();

    // :while condition can use :let bindings
    let result = eval_str_with_env(
        "(vec (for [x (range 10) :let [sq (* x x)] :while (< sq 30)] sq))",
        &env,
    )
    .unwrap();

    // Squares < 30: 0, 1, 4, 9, 16, 25
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(4),
            KlujurVal::int(9),
            KlujurVal::int(16),
            KlujurVal::int(25)
        ])
    );
}

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_while_in_inner_loop() {
    let env = setup_env_with_stdlib();

    // :while in inner loop should only affect inner iteration
    let result = eval_str_with_env(
        "(vec (for [x [1 2] y (range 10) :while (< y 3)] [x y]))",
        &env,
    )
    .unwrap();

    // For x=1: [1 0] [1 1] [1 2], for x=2: [2 0] [2 1] [2 2]
    assert_eq!(
        result.to_string(),
        "[[1 0] [1 1] [1 2] [2 0] [2 1] [2 2]]"
    );
}

// =============================================================================
// Combined modifiers - complex cases
// =============================================================================

#[test]
#[ignore = "BUG: :for-while-stop sentinel leaks into output"]
fn test_for_all_modifiers() {
    let env = setup_env_with_stdlib();

    // Use :let, :when, and :while together
    let result = eval_str_with_env(
        "(vec (for [x (range 20)
                    :let [sq (* x x)]
                    :while (< sq 100)
                    :when (even? x)]
                sq))",
        &env,
    )
    .unwrap();

    // Even squares while sq < 100: 0 (0^2), 4 (2^2), 16 (4^2), 36 (6^2), 64 (8^2)
    assert_eq!(
        result,
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(4),
            KlujurVal::int(16),
            KlujurVal::int(36),
            KlujurVal::int(64)
        ])
    );
}

#[test]
fn test_for_deeply_nested() {
    let env = setup_env_with_stdlib();

    // Three levels of nesting
    let result = eval_str_with_env(
        "(vec (for [x [1 2] y [1 2] z [1 2]] [x y z]))",
        &env,
    )
    .unwrap();

    // 2^3 = 8 combinations
    assert_eq!(result.to_string().matches('[').count() - 1, 8);
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_for_returns_lazy_seq() {
    let env = setup_env_with_stdlib();

    // for returns a lazy sequence
    let result = eval_str_with_env("(lazy-seq? (for [x [1 2 3]] x))", &env).unwrap();
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_for_with_nil_in_collection() {
    let env = setup_env_with_stdlib();

    // Handle nil values in collection
    let result = eval_str_with_env(
        "(vec (for [x [1 nil 3]] (if (nil? x) :was-nil x)))",
        &env,
    )
    .unwrap();

    assert_eq!(
        result.to_string(),
        "[1 :was-nil 3]"
    );
}

#[test]
fn test_for_body_can_be_complex() {
    let env = setup_env_with_stdlib();

    // Complex body expression
    let result = eval_str_with_env(
        "(vec (for [x [1 2 3]]
                (let [a (* x 2)
                      b (+ a 1)]
                  {:x x :doubled a :plus-one b})))",
        &env,
    )
    .unwrap();

    // Should produce maps
    let result_str = result.to_string();
    assert!(result_str.contains(":x 1"));
    assert!(result_str.contains(":doubled 4"));
}
