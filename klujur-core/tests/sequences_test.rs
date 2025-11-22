// klujur-core - Sequences integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur sequence operations.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser};

fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, &env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
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
// Basic Sequence Access
// =============================================================================

#[test]
fn test_first_on_vector() {
    assert_eval!("(first [1 2 3])", KlujurVal::int(1));
    assert_eval!("(first [:a :b :c])", KlujurVal::keyword(Keyword::new("a")));
}

#[test]
fn test_first_on_list() {
    assert_eval!("(first '(1 2 3))", KlujurVal::int(1));
}

#[test]
fn test_first_on_empty_or_nil() {
    assert_eval!("(first [])", KlujurVal::Nil);
    assert_eval!("(first '())", KlujurVal::Nil);
    assert_eval!("(first nil)", KlujurVal::Nil);
}

#[test]
fn test_first_on_string() {
    assert_eval!("(first \"hello\")", KlujurVal::char('h'));
    assert_eval!("(first \"\")", KlujurVal::Nil);
}

#[test]
fn test_rest_on_vector() {
    assert_eval!(
        "(rest [1 2 3])",
        KlujurVal::list(vec![KlujurVal::int(2), KlujurVal::int(3)])
    );
}

#[test]
fn test_rest_on_list() {
    assert_eval!(
        "(rest '(1 2 3))",
        KlujurVal::list(vec![KlujurVal::int(2), KlujurVal::int(3)])
    );
}

#[test]
fn test_rest_returns_empty_list() {
    // IMPORTANT: rest returns () not nil
    assert_eval!("(rest [])", KlujurVal::empty_list());
    assert_eval!("(rest '())", KlujurVal::empty_list());
    assert_eval!("(rest nil)", KlujurVal::empty_list());
    assert_eval!("(rest [1])", KlujurVal::empty_list());
}

// =============================================================================
// Nil Punning - Critical Clojure Semantics
// =============================================================================

#[test]
fn test_first_returns_nil_for_empty() {
    // first on empty returns nil (falsy)
    assert_eval!("(first [])", KlujurVal::Nil);
    assert_eval!("(first nil)", KlujurVal::Nil);
}

#[test]
fn test_rest_on_single_returns_empty_list() {
    // rest returns () which is truthy!
    assert_eval!("(rest [1])", KlujurVal::empty_list());

    // () is truthy in conditionals
    assert_eval!(
        "(if (rest [1]) :truthy :falsy)",
        KlujurVal::keyword(Keyword::new("truthy"))
    );
}

// =============================================================================
// cons
// =============================================================================

#[test]
fn test_cons_adds_to_front() {
    assert_eval!(
        "(cons 0 [1 2 3])",
        KlujurVal::list(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
    assert_eval!(
        "(cons 0 '(1 2 3))",
        KlujurVal::list(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_cons_on_nil() {
    assert_eval!("(cons 1 nil)", KlujurVal::list(vec![KlujurVal::int(1)]));
}

// =============================================================================
// count
// =============================================================================

#[test]
fn test_count_on_various_collections() {
    assert_eval!("(count nil)", KlujurVal::int(0));
    assert_eval!("(count [])", KlujurVal::int(0));
    assert_eval!("(count [1 2 3])", KlujurVal::int(3));
    assert_eval!("(count '())", KlujurVal::int(0));
    assert_eval!("(count '(1 2 3))", KlujurVal::int(3));
    assert_eval!("(count {})", KlujurVal::int(0));
    assert_eval!("(count {:a 1 :b 2})", KlujurVal::int(2));
    assert_eval!("(count #{})", KlujurVal::int(0));
    assert_eval!("(count #{1 2 3})", KlujurVal::int(3));
}

#[test]
fn test_count_on_string() {
    assert_eval!("(count \"\")", KlujurVal::int(0));
    assert_eval!("(count \"hello\")", KlujurVal::int(5));
}

// =============================================================================
// nth
// =============================================================================

#[test]
fn test_nth_on_vector() {
    assert_eval!("(nth [1 2 3] 0)", KlujurVal::int(1));
    assert_eval!("(nth [1 2 3] 1)", KlujurVal::int(2));
    assert_eval!("(nth [1 2 3] 2)", KlujurVal::int(3));
}

#[test]
fn test_nth_on_list() {
    assert_eval!("(nth '(1 2 3) 0)", KlujurVal::int(1));
    assert_eval!("(nth '(1 2 3) 1)", KlujurVal::int(2));
}

#[test]
fn test_nth_with_default() {
    assert_eval!(
        "(nth [1 2] 5 :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
    assert_eval!(
        "(nth '(1 2) 5 :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

#[test]
fn test_nth_on_string() {
    assert_eval!("(nth \"hello\" 0)", KlujurVal::char('h'));
    assert_eval!("(nth \"hello\" 4)", KlujurVal::char('o'));
    assert_eval!(
        "(nth \"hi\" 5 :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

// =============================================================================
// Sequence Predicates
// =============================================================================

#[test]
fn test_seq_predicate() {
    // seq? tests if something is a sequential list/seq
    assert_eval!("(seq? '())", KlujurVal::bool(true));
    assert_eval!("(seq? '(1 2 3))", KlujurVal::bool(true));
    // Vectors are not seqs (they're vectors)
    assert_eval!("(seq? [])", KlujurVal::bool(false));
    assert_eval!("(seq? nil)", KlujurVal::bool(false));
}

// =============================================================================
// empty?
// =============================================================================

#[test]
fn test_empty_on_sequences() {
    assert_eval!("(empty? [])", KlujurVal::bool(true));
    assert_eval!("(empty? '())", KlujurVal::bool(true));
    assert_eval!("(empty? nil)", KlujurVal::bool(true));
    assert_eval!("(empty? [1])", KlujurVal::bool(false));
    assert_eval!("(empty? '(1))", KlujurVal::bool(false));
}

#[test]
fn test_empty_on_string() {
    assert_eval!("(empty? \"\")", KlujurVal::bool(true));
    assert_eval!("(empty? \"a\")", KlujurVal::bool(false));
}

// =============================================================================
// Combining first, rest, cons
// =============================================================================

#[test]
fn test_rebuilding_list() {
    // (cons (first xs) (rest xs)) should equal original for non-empty
    assert_eval!(
        "(cons (first [1 2 3]) (rest [1 2 3]))",
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_recursive_pattern() {
    // Common pattern: checking for empty with first returning nil
    let env = Env::new();
    register_builtins(&env);

    // Define a sum function
    let def_result = {
        let mut parser =
            Parser::new("(def sum (fn* [xs] (if (empty? xs) 0 (+ (first xs) (sum (rest xs))))))")
                .unwrap();
        let expr = parser.parse().unwrap().unwrap();
        eval(&expr, &env)
    };
    assert!(def_result.is_ok());

    // Test it
    let mut parser = Parser::new("(sum [1 2 3 4 5])").unwrap();
    let expr = parser.parse().unwrap().unwrap();
    let result = eval(&expr, &env).unwrap();
    assert_eq!(result, KlujurVal::int(15));
}

// =============================================================================
// Strings as Sequences
// =============================================================================

#[test]
fn test_string_first() {
    assert_eval!("(first \"abc\")", KlujurVal::char('a'));
    assert_eval!("(first \"\")", KlujurVal::Nil);
}

#[test]
fn test_string_count() {
    assert_eval!("(count \"hello\")", KlujurVal::int(5));
    assert_eval!("(count \"\")", KlujurVal::int(0));
}

// =============================================================================
// Identity function
// =============================================================================

#[test]
fn test_identity() {
    assert_eval!("(identity 42)", KlujurVal::int(42));
    assert_eval!("(identity nil)", KlujurVal::Nil);
    assert_eval!(
        "(identity [1 2 3])",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}
