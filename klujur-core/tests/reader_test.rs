// klujur-core - Reader integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for the Klujur reader/parser.
//!
//! These tests verify that parsing and evaluation produce correct results,
//! adapted from the .cljc test suite.

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{Keyword, KlujurVal, Parser, Symbol};

/// Helper to evaluate a string and return the result.
fn eval_str(s: &str) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_str_with_env(s, &env)
}

fn eval_str_with_env(s: &str, env: &Env) -> Result<KlujurVal, String> {
    let mut parser = Parser::new(s).map_err(|e| e.to_string())?;
    match parser.parse().map_err(|e| e.to_string())? {
        Some(expr) => eval(&expr, env).map_err(|e| e.to_string()),
        None => Ok(KlujurVal::Nil),
    }
}

/// Assert that evaluating `input` produces the expected value.
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
// Nil and Booleans
// =============================================================================

#[test]
fn test_nil_literal() {
    assert_eval!("nil", KlujurVal::Nil);
}

#[test]
fn test_boolean_literals() {
    assert_eval!("true", KlujurVal::bool(true));
    assert_eval!("false", KlujurVal::bool(false));
}

// =============================================================================
// Numbers
// =============================================================================

#[test]
fn test_positive_integers() {
    assert_eval!("0", KlujurVal::int(0));
    assert_eval!("1", KlujurVal::int(1));
    assert_eval!("42", KlujurVal::int(42));
    assert_eval!("1000", KlujurVal::int(1000));
    assert_eval!("9999999999", KlujurVal::int(9999999999));
}

#[test]
fn test_negative_integers() {
    assert_eval!("-1", KlujurVal::int(-1));
    assert_eval!("-42", KlujurVal::int(-42));
    assert_eval!("-1000", KlujurVal::int(-1000));
}

#[test]
fn test_integer_bases() {
    assert_eval!("0x10", KlujurVal::int(16));
    assert_eval!("0xff", KlujurVal::int(255));
    assert_eval!("0xFF", KlujurVal::int(255));
    assert_eval!("010", KlujurVal::int(8));
    assert_eval!("2r1010", KlujurVal::int(10));
    assert_eval!("8r77", KlujurVal::int(63));
    assert_eval!("16rff", KlujurVal::int(255));
    assert_eval!("36rz", KlujurVal::int(35));
}

#[test]
fn test_basic_floats() {
    assert_eval!("0.0", KlujurVal::float(0.0));
    assert_eval!("1.0", KlujurVal::float(1.0));
    assert_eval!("3.14", KlujurVal::float(3.14));
    assert_eval!("-2.5", KlujurVal::float(-2.5));
}

#[test]
fn test_scientific_notation() {
    assert_eval!("1e10", KlujurVal::float(1e10));
    assert_eval!("1E10", KlujurVal::float(1e10));
    assert_eval!("1.5e10", KlujurVal::float(1.5e10));
    assert_eval!("1e-10", KlujurVal::float(1e-10));
    assert_eval!("1.5E-3", KlujurVal::float(0.0015));
}

#[test]
fn test_ratios() {
    // Ratios that reduce to integers
    assert_eval!("2/2", KlujurVal::int(1));
    assert_eval!("4/2", KlujurVal::int(2));
    // Ratios that stay as ratios
    assert_eval!("1/2", KlujurVal::Ratio(1, 2));
    assert_eval!("3/4", KlujurVal::Ratio(3, 4));
    // Ratio reduction
    assert_eval!("2/4", KlujurVal::Ratio(1, 2));
}

#[test]
fn test_special_floats() {
    let inf = eval_str("##Inf").unwrap();
    let neg_inf = eval_str("##-Inf").unwrap();
    let nan = eval_str("##NaN").unwrap();

    match inf {
        KlujurVal::Float(f) => assert!(f.is_infinite() && f > 0.0),
        _ => panic!("Expected positive infinity"),
    }
    match neg_inf {
        KlujurVal::Float(f) => assert!(f.is_infinite() && f < 0.0),
        _ => panic!("Expected negative infinity"),
    }
    match nan {
        KlujurVal::Float(f) => assert!(f.is_nan()),
        _ => panic!("Expected NaN"),
    }
}

// =============================================================================
// Characters
// =============================================================================

#[test]
fn test_basic_characters() {
    assert_eval!("\\a", KlujurVal::char('a'));
    assert_eval!("\\z", KlujurVal::char('z'));
    assert_eval!("\\A", KlujurVal::char('A'));
    assert_eval!("\\0", KlujurVal::char('0'));
    assert_eval!("\\9", KlujurVal::char('9'));
}

#[test]
fn test_special_characters() {
    assert_eval!("\\newline", KlujurVal::char('\n'));
    assert_eval!("\\space", KlujurVal::char(' '));
    assert_eval!("\\tab", KlujurVal::char('\t'));
    assert_eval!("\\return", KlujurVal::char('\r'));
    assert_eval!("\\backspace", KlujurVal::char('\x08'));
    assert_eval!("\\formfeed", KlujurVal::char('\x0C'));
}

#[test]
fn test_unicode_characters() {
    assert_eval!("\\u0041", KlujurVal::char('A'));
    assert_eval!("\\u03BB", KlujurVal::char('\u{03BB}')); // lambda
}

// =============================================================================
// Strings
// =============================================================================

#[test]
fn test_basic_strings() {
    assert_eval!("\"\"", KlujurVal::string(""));
    assert_eval!("\"hello\"", KlujurVal::string("hello"));
    assert_eval!("\"Hello, World!\"", KlujurVal::string("Hello, World!"));
}

#[test]
fn test_string_escapes() {
    assert_eval!("\"\\n\"", KlujurVal::string("\n"));
    assert_eval!("\"\\t\"", KlujurVal::string("\t"));
    assert_eval!("\"\\r\"", KlujurVal::string("\r"));
    assert_eval!("\"\\\\\"", KlujurVal::string("\\"));
    assert_eval!("\"\\\"\"", KlujurVal::string("\""));
}

#[test]
fn test_multiline_strings() {
    assert_eval!("\"line1\nline2\"", KlujurVal::string("line1\nline2"));
}

// =============================================================================
// Symbols
// =============================================================================

#[test]
fn test_quoted_symbols() {
    assert_eval!("'foo", KlujurVal::symbol(Symbol::new("foo")));
    assert_eval!("'bar", KlujurVal::symbol(Symbol::new("bar")));
    assert_eval!("'my-symbol", KlujurVal::symbol(Symbol::new("my-symbol")));
}

#[test]
fn test_namespaced_symbols() {
    assert_eval!(
        "'user/foo",
        KlujurVal::symbol(Symbol::with_namespace("user", "foo"))
    );
}

#[test]
fn test_special_symbols() {
    assert_eval!("'+", KlujurVal::symbol(Symbol::new("+")));
    assert_eval!("'-", KlujurVal::symbol(Symbol::new("-")));
    assert_eval!("'*", KlujurVal::symbol(Symbol::new("*")));
    assert_eval!("'/", KlujurVal::symbol(Symbol::new("/")));
    assert_eval!("'<", KlujurVal::symbol(Symbol::new("<")));
    assert_eval!("'>", KlujurVal::symbol(Symbol::new(">")));
}

// =============================================================================
// Keywords
// =============================================================================

#[test]
fn test_simple_keywords() {
    assert_eval!(":foo", KlujurVal::keyword(Keyword::new("foo")));
    assert_eval!(":bar", KlujurVal::keyword(Keyword::new("bar")));
    assert_eval!(":my-key", KlujurVal::keyword(Keyword::new("my-key")));
}

#[test]
fn test_namespaced_keywords() {
    assert_eval!(
        ":user/foo",
        KlujurVal::keyword(Keyword::with_namespace("user", "foo"))
    );
}

// =============================================================================
// Lists
// =============================================================================

#[test]
fn test_empty_list() {
    assert_eval!("'()", KlujurVal::empty_list());
}

#[test]
fn test_quoted_lists() {
    assert_eval!(
        "'(1 2 3)",
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_nested_lists() {
    assert_eval!(
        "'((1 2) (3 4))",
        KlujurVal::list(vec![
            KlujurVal::list(vec![KlujurVal::int(1), KlujurVal::int(2)]),
            KlujurVal::list(vec![KlujurVal::int(3), KlujurVal::int(4)]),
        ])
    );
}

// =============================================================================
// Vectors
// =============================================================================

#[test]
fn test_empty_vector() {
    assert_eval!("[]", KlujurVal::empty_vector());
}

#[test]
fn test_vectors() {
    assert_eval!(
        "[1 2 3]",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_nested_vectors() {
    assert_eval!(
        "[[1 2] [3 4]]",
        KlujurVal::vector(vec![
            KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)]),
            KlujurVal::vector(vec![KlujurVal::int(3), KlujurVal::int(4)]),
        ])
    );
}

// =============================================================================
// Maps
// =============================================================================

#[test]
fn test_empty_map() {
    assert_eval!("{}", KlujurVal::empty_map());
}

#[test]
fn test_maps() {
    let result = eval_str("{:a 1 :b 2}").unwrap();
    if let KlujurVal::Map(map, _) = result {
        assert_eq!(map.len(), 2);
        assert_eq!(
            map.get(&KlujurVal::keyword(Keyword::new("a"))),
            Some(&KlujurVal::int(1))
        );
        assert_eq!(
            map.get(&KlujurVal::keyword(Keyword::new("b"))),
            Some(&KlujurVal::int(2))
        );
    } else {
        panic!("Expected map");
    }
}

// =============================================================================
// Sets
// =============================================================================

#[test]
fn test_empty_set() {
    assert_eval!("#{}", KlujurVal::empty_set());
}

#[test]
fn test_sets() {
    let result = eval_str("#{1 2 3}").unwrap();
    if let KlujurVal::Set(set, _) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&KlujurVal::int(1)));
        assert!(set.contains(&KlujurVal::int(2)));
        assert!(set.contains(&KlujurVal::int(3)));
    } else {
        panic!("Expected set");
    }
}

// =============================================================================
// Whitespace and Comments
// =============================================================================

#[test]
fn test_whitespace() {
    assert_eval!(
        "[1   2   3]",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_commas_as_whitespace() {
    assert_eval!(
        "[1, 2, 3]",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_comments() {
    assert_eval!("42 ; this is a comment", KlujurVal::int(42));
    assert_eval!(
        "[1 ; comment\n2]",
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(2)])
    );
}

#[test]
fn test_discard() {
    assert_eval!(
        "[1 #_2 3]",
        KlujurVal::vector(vec![KlujurVal::int(1), KlujurVal::int(3)])
    );
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_empty_input() {
    assert_eval!("", KlujurVal::Nil);
}

#[test]
fn test_whitespace_only() {
    assert_eval!("   \n\t  ", KlujurVal::Nil);
}

#[test]
fn test_deeply_nested() {
    assert_eval!(
        "[[[[[1]]]]]",
        KlujurVal::vector(vec![KlujurVal::vector(vec![KlujurVal::vector(vec![
            KlujurVal::vector(vec![KlujurVal::vector(vec![KlujurVal::int(1)])])
        ])])])
    );
}
