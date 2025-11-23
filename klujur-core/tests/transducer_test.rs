// klujur-core - Transducer integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur transducers.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_core::init_stdlib;
use klujur_parser::{Keyword, KlujurVal, Parser};

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
// Reduced Type Tests
// =============================================================================

#[test]
fn test_reduced_basic() {
    assert_eval!("(reduced 42)", KlujurVal::reduced(KlujurVal::int(42)));
    assert_eval!("(reduced? (reduced 42))", KlujurVal::bool(true));
    assert_eval!("(reduced? 42)", KlujurVal::bool(false));
}

#[test]
fn test_unreduced() {
    assert_eval!("(unreduced (reduced 42))", KlujurVal::int(42));
    assert_eval!("(unreduced 42)", KlujurVal::int(42));
}

#[test]
fn test_ensure_reduced() {
    // Already reduced stays reduced
    assert_eval!(
        "(reduced? (ensure-reduced (reduced 42)))",
        KlujurVal::bool(true)
    );
    // Not reduced gets wrapped
    assert_eval!("(reduced? (ensure-reduced 42))", KlujurVal::bool(true));
    assert_eval!("(unreduced (ensure-reduced 42))", KlujurVal::int(42));
}

#[test]
fn test_reduce_early_termination() {
    // reduce should stop early when it gets a reduced value
    assert_eval!(
        "(reduce (fn [acc x] (if (= x 3) (reduced acc) (conj acc x))) [] [1 2 3 4 5])",
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

// =============================================================================
// Volatile Tests
// =============================================================================

#[test]
fn test_volatile_basic() {
    assert_eval!("(volatile? (volatile! 0))", KlujurVal::bool(true));
    assert_eval!("(volatile? 42)", KlujurVal::bool(false));
}

#[test]
fn test_volatile_deref() {
    assert_eval!("(deref (volatile! 42))", KlujurVal::int(42));
    assert_eval!("@(volatile! 42)", KlujurVal::int(42));
}

#[test]
fn test_volatile_vreset() {
    let result = eval_multiple(&["(def v (volatile! 0))", "(vreset! v 42)", "@v"]);
    assert_eq!(result.unwrap(), KlujurVal::int(42));
}

#[test]
fn test_volatile_vswap() {
    let result = eval_multiple(&["(def v (volatile! 0))", "(vswap! v inc)", "@v"]);
    assert_eq!(result.unwrap(), KlujurVal::int(1));

    let result = eval_multiple(&["(def v (volatile! 0))", "(vswap! v + 10)", "@v"]);
    assert_eq!(result.unwrap(), KlujurVal::int(10));
}

// =============================================================================
// Basic Transducer Tests
// =============================================================================

#[test]
fn test_map_transducer() {
    assert_eval!(
        "(into [] (map inc) [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_filter_transducer() {
    assert_eval!(
        "(into [] (filter even?) [1 2 3 4 5])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

#[test]
fn test_remove_transducer() {
    assert_eval!(
        "(into [] (remove even?) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(3),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_transducer_composition() {
    // (comp (map inc) (filter even?)) on [1 2 3 4] should give [2 4]
    assert_eval!(
        "(into [] (comp (map inc) (filter even?)) [1 2 3 4])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

// =============================================================================
// Early Termination Tests
// =============================================================================

#[test]
fn test_take_transducer() {
    assert_eval!(
        "(into [] (take 3) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_take_transducer_from_range() {
    // Should terminate early from infinite range
    assert_eval!(
        "(into [] (take 3) (range 1000000))",
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2)
        ])
    );
}

#[test]
fn test_drop_transducer() {
    assert_eval!(
        "(into [] (drop 2) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_take_while_transducer() {
    assert_eval!(
        "(into [] (take-while #(< % 4)) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_drop_while_transducer() {
    assert_eval!(
        "(into [] (drop-while #(< % 3)) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_take_nth_transducer() {
    assert_eval!(
        "(into [] (take-nth 2) [1 2 3 4 5 6])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(3),
            KlujurVal::int(5)
        ])
    );
}

// =============================================================================
// Keep Transducers
// =============================================================================

#[test]
fn test_keep_transducer() {
    // Keep non-nil results
    assert_eval!(
        "(into [] (keep #(if (even? %) % nil)) [1 2 3 4 5])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

#[test]
fn test_keep_indexed_transducer() {
    // Keep items at even indices
    assert_eval!(
        "(into [] (keep-indexed (fn [i x] (if (even? i) x nil))) [:a :b :c :d])",
        KlujurVal::vector(vec![
            KlujurVal::Keyword(Keyword::new("a")),
            KlujurVal::Keyword(Keyword::new("c"))
        ])
    );
}

#[test]
fn test_map_indexed_transducer() {
    assert_eval!(
        "(into [] (map-indexed vector) [:a :b :c])",
        KlujurVal::vector(vec![
            KlujurVal::vector(vec![
                KlujurVal::int(0),
                KlujurVal::Keyword(Keyword::new("a"))
            ]),
            KlujurVal::vector(vec![
                KlujurVal::int(1),
                KlujurVal::Keyword(Keyword::new("b"))
            ]),
            KlujurVal::vector(vec![
                KlujurVal::int(2),
                KlujurVal::Keyword(Keyword::new("c"))
            ])
        ])
    );
}

// =============================================================================
// Deduplication Transducers
// =============================================================================

#[test]
fn test_dedupe_transducer() {
    assert_eval!(
        "(into [] (dedupe) [1 1 2 2 2 3 1 1])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(1)
        ])
    );
}

#[test]
fn test_distinct_transducer() {
    assert_eval!(
        "(into [] (distinct) [1 2 1 3 2 4])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

// =============================================================================
// Partitioning Transducers
// =============================================================================

#[test]
fn test_partition_all_transducer() {
    assert_eval!(
        "(into [] (partition-all 2) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)]),
            KlujurVal::vector(vec![KlujurVal::int(3), KlujurVal::int(4)]),
            KlujurVal::vector(vec![KlujurVal::int(5)])
        ])
    );
}

#[test]
fn test_partition_by_transducer() {
    assert_eval!(
        "(into [] (partition-by odd?) [1 1 2 2 3 3 4])",
        KlujurVal::vector(vec![
            KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(1)]),
            KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(2)]),
            KlujurVal::vector(vec![KlujurVal::int(3), KlujurVal::int(3)]),
            KlujurVal::vector(vec![KlujurVal::int(4)])
        ])
    );
}

// =============================================================================
// Cat and Mapcat Transducers
// =============================================================================

#[test]
fn test_cat_transducer() {
    // cat is directly a transducer (no parens needed)
    assert_eval!(
        "(into [] cat [[1 2] [3 4] [5]])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_mapcat_transducer() {
    assert_eval!(
        "(into [] (mapcat #(repeat 2 %)) [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Interpose Transducer
// =============================================================================

#[test]
fn test_interpose_transducer() {
    assert_eval!(
        "(into [] (interpose :sep) [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::Keyword(Keyword::new("sep")),
            KlujurVal::int(2),
            KlujurVal::Keyword(Keyword::new("sep")),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Transduce Tests
// =============================================================================

#[test]
fn test_transduce_basic() {
    // (transduce (map inc) + [1 2 3]) => (+ (+ (+ 0 2) 3) 4) => 9
    assert_eval!("(transduce (map inc) + [1 2 3])", KlujurVal::int(9));
}

#[test]
fn test_transduce_with_init() {
    assert_eval!("(transduce (map inc) + 10 [1 2 3])", KlujurVal::int(19));
}

#[test]
fn test_transduce_with_composition() {
    // (inc each) then (filter even?) then sum
    assert_eval!(
        "(transduce (comp (map inc) (filter even?)) + [1 2 3 4])",
        KlujurVal::int(6) // 2 + 4
    );
}

// =============================================================================
// Into 3-arity Tests
// =============================================================================

#[test]
fn test_into_with_transducer() {
    assert_eval!(
        "(into #{} (map inc) [1 2 3])",
        KlujurVal::set(vec![
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

// =============================================================================
// Complex Composition Tests
// =============================================================================

#[test]
fn test_complex_composition() {
    // Filter odds, increment, take first 3
    assert_eval!(
        "(into [] (comp (filter odd?) (map inc) (take 3)) (range 100))",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6)
        ])
    );
}

// =============================================================================
// Completing Tests
// =============================================================================

#[test]
fn test_completing() {
    // completing makes a simple 2-arity function work with transduce
    assert_eval!(
        "(transduce (map inc) (completing +) [1 2 3])",
        KlujurVal::int(9)
    );
}

// =============================================================================
// Sequence with Transducer Tests
// =============================================================================

#[test]
fn test_sequence_with_map() {
    // sequence with transducer produces lazy sequence, convert to vec for comparison
    assert_eval!(
        "(vec (sequence (map inc) [1 2 3]))",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_sequence_with_filter() {
    assert_eval!(
        "(vec (sequence (filter even?) [1 2 3 4 5 6]))",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6)
        ])
    );
}

#[test]
fn test_sequence_with_composition() {
    assert_eval!(
        "(vec (sequence (comp (map inc) (filter even?)) [1 2 3 4]))",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

#[test]
fn test_sequence_with_take() {
    // take should terminate early
    assert_eval!(
        "(vec (sequence (comp (map inc) (take 3)) (range 100)))",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_sequence_without_transducer() {
    // 1-arity just calls seq
    assert_eval!(
        "(vec (sequence [1 2 3]))",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Eduction Tests
// =============================================================================

#[test]
fn test_eduction_creation() {
    assert_eval!(
        "(eduction? (eduction (map inc) [1 2 3]))",
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_eduction_seq() {
    assert_eval!(
        "(vec (eduction-seq (eduction (map inc) [1 2 3])))",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_eduction_reduce() {
    assert_eval!(
        "(eduction-reduce (eduction (map inc) [1 2 3]) + 0)",
        KlujurVal::int(9)
    );
}

#[test]
fn test_eduction_with_composition() {
    assert_eval!(
        "(vec (eduction-seq (eduction (map inc) (filter even?) [1 2 3 4])))",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

// =============================================================================
// Preserving-Reduced Tests (for cat transducer)
// =============================================================================

#[test]
fn test_cat_with_early_termination() {
    // cat should respect reduced from inner sequences
    // Test that take works correctly through cat
    assert_eval!(
        "(into [] (comp cat (take 4)) [[1 2] [3 4] [5 6]])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}
