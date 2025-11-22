// klujur-core - Lazy sequence integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur lazy sequences.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{KlujurVal, Parser};

fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).map_err(|e| e.to_string())?;
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, &env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

fn eval_multiple(strs: &[&str]) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    init_stdlib(&env).map_err(|e| e.to_string())?;
    let mut result = KlujurVal::Nil;
    for s in strs {
        let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
        while let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
            result = eval(&expr, &env).map_err(|e| e.to_string())?;
        }
    }
    Ok(result)
}

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

// =============================================================================
// Basic Lazy Sequence Creation
// =============================================================================

#[test]
fn test_lazy_seq_predicate() {
    assert_eval!("(lazy-seq? (lazy-seq nil))", KlujurVal::bool(true));
    assert_eval!("(lazy-seq? [1 2 3])", KlujurVal::bool(false));
    assert_eval!("(lazy-seq? nil)", KlujurVal::bool(false));
}

#[test]
fn test_lazy_seq_empty() {
    // Empty lazy seq (body returns nil)
    assert_eval!("(seq (lazy-seq nil))", KlujurVal::Nil);
    assert_eval!("(first (lazy-seq nil))", KlujurVal::Nil);
}

#[test]
fn test_lazy_seq_with_list() {
    // Lazy seq wrapping a list
    assert_eval!("(first (lazy-seq '(1 2 3)))", KlujurVal::int(1));
    assert_eval!(
        "(rest (lazy-seq '(1 2 3)))",
        KlujurVal::list(vec![KlujurVal::int(2), KlujurVal::int(3)])
    );
}

#[test]
fn test_lazy_seq_with_vector() {
    // Lazy seq wrapping a vector
    assert_eval!("(first (lazy-seq [1 2 3]))", KlujurVal::int(1));
}

// =============================================================================
// Deferred Evaluation
// =============================================================================

#[test]
fn test_lazy_seq_defers_evaluation() {
    // Creating a lazy seq doesn't evaluate the body
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def lazy (lazy-seq (swap! side-effect inc) [1 2 3]))",
        "@side-effect",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(0));
}

#[test]
fn test_lazy_seq_evaluates_on_access() {
    // Accessing forces evaluation
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def lazy (lazy-seq (swap! side-effect inc) [1 2 3]))",
        "(first lazy)",
        "@side-effect",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(1));
}

#[test]
fn test_lazy_seq_caches_result() {
    // Multiple accesses don't re-evaluate
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def lazy (lazy-seq (swap! side-effect inc) [1 2 3]))",
        "(first lazy)",
        "(first lazy)",
        "(first lazy)",
        "@side-effect",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(1)); // Still 1, not 3
}

// =============================================================================
// realized? Predicate
// =============================================================================

#[test]
fn test_realized_predicate_lazy_seq() {
    let result = eval_multiple(&["(def lazy (lazy-seq [1 2 3]))", "(realized? lazy)"]);
    assert_eq!(result.unwrap(), KlujurVal::bool(false));
}

#[test]
fn test_realized_after_force() {
    let result = eval_multiple(&[
        "(def lazy (lazy-seq [1 2 3]))",
        "(first lazy)", // Force it
        "(realized? lazy)",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::bool(true));
}

#[test]
fn test_realized_non_lazy() {
    // Non-lazy values are always "realized"
    assert_eval!("(realized? [1 2 3])", KlujurVal::bool(true));
    assert_eval!("(realized? nil)", KlujurVal::bool(true));
}

// =============================================================================
// Recursive Lazy Sequences
// =============================================================================

#[test]
fn test_recursive_lazy_seq() {
    // Define integers-from using lazy-seq with def and fn
    let result = eval_multiple(&[
        "(def integers-from (fn [n]
           (lazy-seq (cons n (integers-from (inc n))))))",
        "(first (integers-from 0))",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(0));
}

#[test]
fn test_recursive_lazy_seq_take() {
    // Take from recursive lazy seq
    let result = eval_multiple(&[
        "(def integers-from (fn [n]
           (lazy-seq (cons n (integers-from (inc n))))))",
        "(take 5 (integers-from 0))",
    ]);
    assert_eq!(
        result.unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4),
        ])
    );
}

#[test]
fn test_drop_on_lazy_seq() {
    let result = eval_multiple(&[
        "(def integers-from (fn [n]
           (lazy-seq (cons n (integers-from (inc n))))))",
        "(take 3 (drop 10 (integers-from 0)))",
    ]);
    assert_eq!(
        result.unwrap(),
        KlujurVal::list(vec![
            KlujurVal::int(10),
            KlujurVal::int(11),
            KlujurVal::int(12),
        ])
    );
}

// =============================================================================
// cons with Lazy Sequences
// =============================================================================

#[test]
fn test_cons_to_lazy_seq() {
    let result = eval_multiple(&["(def lazy (lazy-seq '(2 3 4)))", "(first (cons 1 lazy))"]);
    assert_eq!(result.unwrap(), KlujurVal::int(1));
}

#[test]
fn test_cons_preserves_laziness() {
    // cons onto a lazy seq should preserve laziness
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def lazy (lazy-seq (swap! side-effect inc) [2 3 4]))",
        "(def with-head (cons 1 lazy))",
        "@side-effect",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(0)); // Still not forced
}

// =============================================================================
// doall and dorun
// =============================================================================

#[test]
fn test_doall_forces_sequence() {
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def counting-seq (fn []
           (lazy-seq
             (swap! side-effect inc)
             (when (< @side-effect 5)
               (cons @side-effect (counting-seq))))))",
        "(doall (counting-seq))",
        "@side-effect",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(5));
}

#[test]
fn test_dorun_returns_nil() {
    let result = eval_multiple(&[
        "(def side-effect (atom 0))",
        "(def counting-seq (fn []
           (lazy-seq
             (swap! side-effect inc)
             (when (< @side-effect 3)
               (cons @side-effect (counting-seq))))))",
        "(dorun (counting-seq))",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::Nil);
}

// =============================================================================
// seq, next on Lazy Sequences
// =============================================================================

#[test]
fn test_seq_on_lazy_seq() {
    assert_eval!("(seq (lazy-seq nil))", KlujurVal::Nil);
    // Non-empty lazy seq returns itself
    let result = eval_str("(seq? (seq (lazy-seq [1 2 3])))");
    // seq on lazy-seq returns the lazy seq if non-empty
    assert!(result.is_ok());
}

#[test]
fn test_next_on_lazy_seq() {
    let result = eval_multiple(&[
        "(def integers-from (fn [n]
           (lazy-seq (cons n (integers-from (inc n))))))",
        "(first (next (integers-from 0)))",
    ]);
    assert_eq!(result.unwrap(), KlujurVal::int(1));
}

// =============================================================================
// Integration with Higher-Order Functions
// =============================================================================

#[test]
fn test_map_on_lazy_seq() {
    // Test map on a finite lazy seq - map returns a lazy seq, so use vec to realize
    let result = eval_multiple(&[
        "(def make-lazy (fn [coll]
           (lazy-seq (when (seq coll)
             (cons (first coll) (make-lazy (rest coll)))))))",
        "(vec (map inc (make-lazy [0 1 2])))",
    ]);
    assert_eq!(
        result.unwrap(),
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
        ])
    );
}

#[test]
fn test_filter_on_lazy_seq() {
    // Test filter on a finite lazy seq - filter returns a lazy seq, so use vec to realize
    let result = eval_multiple(&[
        "(def make-lazy (fn [coll]
           (lazy-seq (when (seq coll)
             (cons (first coll) (make-lazy (rest coll)))))))",
        "(vec (filter even? (make-lazy [0 1 2 3 4])))",
    ]);
    assert_eq!(
        result.unwrap(),
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(2),
            KlujurVal::int(4),
        ])
    );
}
