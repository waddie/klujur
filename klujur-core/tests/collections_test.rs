// klujur-core - Collections integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur collection operations.

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

macro_rules! assert_eval_err {
    ($input:expr) => {
        let result = eval_str($input);
        assert!(
            result.is_err(),
            "Expected error for '{}' but got {:?}",
            $input,
            result.ok()
        );
    };
}

// =============================================================================
// Lists
// =============================================================================

#[test]
fn test_list_creation() {
    assert_eval!("(list)", KlujurVal::empty_list());
    assert_eval!("(list 1)", KlujurVal::list(vec![KlujurVal::int(1)]));
    assert_eval!(
        "(list 1 2 3)",
        KlujurVal::list(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_list_evaluates_arguments() {
    assert_eval!(
        "(list (+ 1 1) (+ 2 2) (+ 3 3))",
        KlujurVal::list(vec![
            KlujurVal::int(2),
            KlujurVal::int(4),
            KlujurVal::int(6)
        ])
    );
}

#[test]
fn test_list_predicate() {
    assert_eval!("(list? '())", KlujurVal::bool(true));
    assert_eval!("(list? '(1 2 3))", KlujurVal::bool(true));
    assert_eval!("(list? (list 1 2))", KlujurVal::bool(true));
    assert_eval!("(list? [])", KlujurVal::bool(false));
    assert_eval!("(list? nil)", KlujurVal::bool(false));
}

#[test]
fn test_list_count() {
    assert_eval!("(count '())", KlujurVal::int(0));
    assert_eval!("(count '(1))", KlujurVal::int(1));
    assert_eval!("(count '(1 2 3))", KlujurVal::int(3));
}

#[test]
fn test_list_nth() {
    assert_eval!("(nth '(1 2 3) 0)", KlujurVal::int(1));
    assert_eval!("(nth '(1 2 3) 1)", KlujurVal::int(2));
    assert_eval!("(nth '(1 2 3) 2)", KlujurVal::int(3));
}

#[test]
fn test_list_nth_with_default() {
    assert_eval!(
        "(nth '(1 2) 5 :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

#[test]
fn test_list_nth_out_of_bounds() {
    assert_eval_err!("(nth '(1 2) 5)");
}

#[test]
fn test_list_conj() {
    // conj on list adds to front
    assert_eval!(
        "(conj '(1 2 3) 0)",
        KlujurVal::list(vec![
            KlujurVal::int(0),
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
    assert_eval!("(conj '() 1)", KlujurVal::list(vec![KlujurVal::int(1)]));
}

// =============================================================================
// Vectors
// =============================================================================

#[test]
fn test_vector_creation() {
    assert_eval!("(vector)", KlujurVal::empty_vector());
    assert_eval!("(vector 1)", KlujurVal::vector(vec![KlujurVal::int(1)]));
    assert_eval!(
        "(vector 1 2 3)",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3)
        ])
    );
}

#[test]
fn test_vector_predicate() {
    assert_eval!("(vector? [])", KlujurVal::bool(true));
    assert_eval!("(vector? [1 2 3])", KlujurVal::bool(true));
    assert_eval!("(vector? '(1 2 3))", KlujurVal::bool(false));
    assert_eval!("(vector? nil)", KlujurVal::bool(false));
}

#[test]
fn test_vector_count() {
    assert_eval!("(count [])", KlujurVal::int(0));
    assert_eval!("(count [1])", KlujurVal::int(1));
    assert_eval!("(count [1 2 3])", KlujurVal::int(3));
}

#[test]
fn test_vector_nth() {
    assert_eval!("(nth [1 2 3] 0)", KlujurVal::int(1));
    assert_eval!("(nth [1 2 3] 1)", KlujurVal::int(2));
    assert_eval!("(nth [1 2 3] 2)", KlujurVal::int(3));
}

#[test]
fn test_vector_get() {
    assert_eval!("(get [1 2 3] 0)", KlujurVal::int(1));
    assert_eval!("(get [1 2 3] 1)", KlujurVal::int(2));
    assert_eval!("(get [1 2 3] 5)", KlujurVal::Nil);
    assert_eval!(
        "(get [1 2] 5 :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

#[test]
fn test_vector_conj() {
    // conj on vector adds to end
    assert_eval!(
        "(conj [1 2 3] 4)",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::int(2),
            KlujurVal::int(3),
            KlujurVal::int(4)
        ])
    );
    assert_eval!("(conj [] 1)", KlujurVal::vector(vec![KlujurVal::int(1)]));
}

#[test]
fn test_vector_assoc() {
    assert_eval!(
        "(assoc [1 2 3] 1 :x)",
        KlujurVal::vector(vec![
            KlujurVal::int(1),
            KlujurVal::keyword(Keyword::new("x")),
            KlujurVal::int(3)
        ])
    );
}

// =============================================================================
// Maps
// =============================================================================

#[test]
fn test_map_predicate() {
    assert_eval!("(map? {})", KlujurVal::bool(true));
    assert_eval!("(map? {:a 1})", KlujurVal::bool(true));
    assert_eval!("(map? [])", KlujurVal::bool(false));
    assert_eval!("(map? nil)", KlujurVal::bool(false));
}

#[test]
fn test_map_count() {
    assert_eval!("(count {})", KlujurVal::int(0));
    assert_eval!("(count {:a 1})", KlujurVal::int(1));
    assert_eval!("(count {:a 1 :b 2})", KlujurVal::int(2));
}

#[test]
fn test_map_get() {
    assert_eval!("(get {:a 1 :b 2} :a)", KlujurVal::int(1));
    assert_eval!("(get {:a 1 :b 2} :b)", KlujurVal::int(2));
    assert_eval!("(get {:a 1} :c)", KlujurVal::Nil);
    assert_eval!(
        "(get {:a 1} :c :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

#[test]
fn test_keyword_as_function() {
    assert_eval!("(:a {:a 1 :b 2})", KlujurVal::int(1));
    assert_eval!("(:b {:a 1 :b 2})", KlujurVal::int(2));
    assert_eval!("(:c {:a 1})", KlujurVal::Nil);
    assert_eval!(
        "(:c {:a 1} :default)",
        KlujurVal::keyword(Keyword::new("default"))
    );
}

#[test]
fn test_map_assoc() {
    let result = eval_str("(assoc {:a 1} :b 2)").unwrap();
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

#[test]
fn test_map_assoc_replaces() {
    let result = eval_str("(assoc {:a 1} :a 10)").unwrap();
    if let KlujurVal::Map(map, _) = result {
        assert_eq!(map.len(), 1);
        assert_eq!(
            map.get(&KlujurVal::keyword(Keyword::new("a"))),
            Some(&KlujurVal::int(10))
        );
    } else {
        panic!("Expected map");
    }
}

#[test]
fn test_map_dissoc() {
    let result = eval_str("(dissoc {:a 1 :b 2} :a)").unwrap();
    if let KlujurVal::Map(map, _) = result {
        assert_eq!(map.len(), 1);
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
fn test_set_predicate() {
    assert_eval!("(set? #{})", KlujurVal::bool(true));
    assert_eval!("(set? #{1 2})", KlujurVal::bool(true));
    assert_eval!("(set? [])", KlujurVal::bool(false));
    assert_eval!("(set? nil)", KlujurVal::bool(false));
}

#[test]
fn test_set_count() {
    assert_eval!("(count #{})", KlujurVal::int(0));
    assert_eval!("(count #{1})", KlujurVal::int(1));
    assert_eval!("(count #{1 2 3})", KlujurVal::int(3));
}

#[test]
fn test_set_get() {
    // get on set returns the element if present, nil otherwise
    assert_eval!("(get #{1 2 3} 1)", KlujurVal::int(1));
    assert_eval!("(get #{1 2 3} 4)", KlujurVal::Nil);
}

#[test]
fn test_set_conj() {
    let result = eval_str("(conj #{1 2} 3)").unwrap();
    if let KlujurVal::Set(set, _) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&KlujurVal::int(1)));
        assert!(set.contains(&KlujurVal::int(2)));
        assert!(set.contains(&KlujurVal::int(3)));
    } else {
        panic!("Expected set");
    }
}

#[test]
fn test_set_conj_no_duplicate() {
    let result = eval_str("(conj #{1 2} 2)").unwrap();
    if let KlujurVal::Set(set, _) = result {
        assert_eq!(set.len(), 2); // Still 2, not 3
    } else {
        panic!("Expected set");
    }
}

// =============================================================================
// General Collection Functions
// =============================================================================

#[test]
fn test_empty_predicate() {
    assert_eval!("(empty? [])", KlujurVal::bool(true));
    assert_eval!("(empty? '())", KlujurVal::bool(true));
    assert_eval!("(empty? {})", KlujurVal::bool(true));
    assert_eval!("(empty? #{})", KlujurVal::bool(true));
    assert_eval!("(empty? nil)", KlujurVal::bool(true));
    assert_eval!("(empty? [1])", KlujurVal::bool(false));
    assert_eval!("(empty? {:a 1})", KlujurVal::bool(false));
}

#[test]
fn test_coll_predicate() {
    assert_eval!("(coll? [])", KlujurVal::bool(true));
    assert_eval!("(coll? '())", KlujurVal::bool(true));
    assert_eval!("(coll? {})", KlujurVal::bool(true));
    assert_eval!("(coll? #{})", KlujurVal::bool(true));
    assert_eval!("(coll? nil)", KlujurVal::bool(false));
    assert_eval!("(coll? 1)", KlujurVal::bool(false));
    assert_eval!("(coll? \"string\")", KlujurVal::bool(false));
}

#[test]
fn test_conj_on_nil() {
    // conj on nil creates a list
    assert_eval!("(conj nil 1)", KlujurVal::list(vec![KlujurVal::int(1)]));
}
