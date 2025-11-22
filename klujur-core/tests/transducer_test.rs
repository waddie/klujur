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
fn test_map_xf() {
    assert_eval!(
        "(into [] (map-xf inc) [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
}

#[test]
fn test_filter_xf() {
    assert_eval!(
        "(into [] (filter-xf even?) [1 2 3 4 5])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

#[test]
fn test_remove_xf() {
    assert_eval!(
        "(into [] (remove-xf even?) [1 2 3 4 5])",
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
        "(into [] (comp (map-xf inc) (filter-xf even?)) [1 2 3 4])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

// =============================================================================
// Early Termination Tests
// =============================================================================

#[test]
fn test_take_xf() {
    assert_eval!(
        "(into [] (take-xf 3) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_take_xf_from_range() {
    // Should terminate early from infinite range
    assert_eval!(
        "(into [] (take-xf 3) (range 1000000))",
        KlujurVal::vector(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2)
        ])
    );
}

#[test]
fn test_drop_xf() {
    assert_eval!(
        "(into [] (drop-xf 2) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_take_while_xf() {
    assert_eval!(
        "(into [] (take-while-xf #(< % 4)) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_drop_while_xf() {
    assert_eval!(
        "(into [] (drop-while-xf #(< % 3)) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::int(3),
            KlujurVal::int(4),
            KlujurVal::int(5)
        ])
    );
}

#[test]
fn test_take_nth_xf() {
    assert_eval!(
        "(into [] (take-nth-xf 2) [1 2 3 4 5 6])",
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
fn test_keep_xf() {
    // Keep non-nil results
    assert_eval!(
        "(into [] (keep-xf #(if (even? %) % nil)) [1 2 3 4 5])",
        KlujurVal::vector(vec![KlujurVal::int(2), KlujurVal::int(4)])
    );
}

#[test]
fn test_keep_indexed_xf() {
    // Keep items at even indices
    assert_eval!(
        "(into [] (keep-indexed-xf (fn [i x] (if (even? i) x nil))) [:a :b :c :d])",
        KlujurVal::vector(vec![
            KlujurVal::Keyword(Keyword::new("a")),
            KlujurVal::Keyword(Keyword::new("c"))
        ])
    );
}

#[test]
fn test_map_indexed_xf() {
    assert_eval!(
        "(into [] (map-indexed-xf vector) [:a :b :c])",
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
fn test_dedupe_xf() {
    assert_eval!(
        "(into [] (dedupe-xf) [1 1 2 2 2 3 1 1])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(1)
        ])
    );
}

#[test]
fn test_distinct_xf() {
    assert_eval!(
        "(into [] (distinct-xf) [1 2 1 3 2 4])",
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
fn test_partition_all_xf() {
    assert_eval!(
        "(into [] (partition-all-xf 2) [1 2 3 4 5])",
        KlujurVal::vector(vec![
            KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)]),
            KlujurVal::vector(vec![KlujurVal::int(3), KlujurVal::int(4)]),
            KlujurVal::vector(vec![KlujurVal::int(5)])
        ])
    );
}

#[test]
fn test_partition_by_xf() {
    assert_eval!(
        "(into [] (partition-by-xf odd?) [1 1 2 2 3 3 4])",
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
fn test_cat_xf() {
    assert_eval!(
        "(into [] (cat-xf) [[1 2] [3 4] [5]])",
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
fn test_mapcat_xf() {
    assert_eval!(
        "(into [] (mapcat-xf #(repeat 2 %)) [1 2 3])",
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
fn test_interpose_xf() {
    assert_eval!(
        "(into [] (interpose-xf :sep) [1 2 3])",
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
    assert_eval!("(transduce (map-xf inc) + [1 2 3])", KlujurVal::int(9));
}

#[test]
fn test_transduce_with_init() {
    assert_eval!("(transduce (map-xf inc) + 10 [1 2 3])", KlujurVal::int(19));
}

#[test]
fn test_transduce_with_composition() {
    // (inc each) then (filter even?) then sum
    assert_eval!(
        "(transduce (comp (map-xf inc) (filter-xf even?)) + [1 2 3 4])",
        KlujurVal::int(6) // 2 + 4
    );
}

// =============================================================================
// Into 3-arity Tests
// =============================================================================

#[test]
fn test_into_with_transducer() {
    assert_eval!(
        "(into #{} (map-xf inc) [1 2 3])",
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
        "(into [] (comp (filter-xf odd?) (map-xf inc) (take-xf 3)) (range 100))",
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
        "(transduce (map-xf inc) (completing +) [1 2 3])",
        KlujurVal::int(9)
    );
}
