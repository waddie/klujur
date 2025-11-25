// klujur-core - Integration tests for the klujur.test framework
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Tests for the klujur.test testing framework.

mod common;

use common::{eval_all, new_env_with_stdlib};
use klujur_core::KlujurVal;

#[test]
fn test_require_klujur_test() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test])
        (atom? klujur.test/*tests*)
        "#,
        &env,
    )
    .unwrap();
    // *tests* should be an atom (proves namespace loaded)
    assert_eq!(result, KlujurVal::bool(true));
}

#[test]
fn test_deftest_registers_test() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is]])
        (deftest my-first-test
          (is (= 4 (+ 2 2))))
        (get @klujur.test/*tests* 'user)
        "#,
        &env,
    )
    .unwrap();

    // Should return a map containing my-first-test
    if let KlujurVal::Map(m, _) = result {
        assert!(m.len() == 1, "Expected 1 test registered");
    } else {
        panic!("Expected a map, got {:?}", result);
    }
}

#[test]
fn test_is_equality_passes() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is run-tests]])
        (deftest equality-test
          (is (= 4 (+ 2 2)))
          (is (= [1 2 3] [1 2 3]))
          (is (= {:a 1} {:a 1})))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    // Result should be {:pass 3 :fail 0 :error 0 :failures []}
    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        let fail = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("fail")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(3));
        assert_eq!(*fail, KlujurVal::int(0));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_is_equality_fails() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is run-tests]])
        (deftest fail-test
          (is (= 5 (+ 2 2))))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        let fail = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("fail")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(0));
        assert_eq!(*fail, KlujurVal::int(1));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_is_truthy() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is run-tests]])
        (deftest truthy-test
          (is true)
          (is (not nil))
          (is (seq [1 2 3])))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(3));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_is_thrown() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is run-tests]])
        (deftest thrown-test
          (is (thrown? Exception (throw "error")))
          (is (thrown? Exception (/ 1 0))))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(2));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_testing_context() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is testing run-tests]])
        (deftest context-test
          (testing "outer context"
            (testing "inner context"
              (is (= 4 (+ 2 2))))))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(1));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_are_macro() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest are run-tests]])
        (deftest are-test
          (are [x y] (= x y)
            2 (+ 1 1)
            4 (* 2 2)
            6 (+ 2 2 2)))
        (run-tests 'user)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(3));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_run_all_tests() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is run-all-tests]])
        (deftest test-one (is (= 1 1)))
        (deftest test-two (is (= 2 2)))
        (run-all-tests)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        assert_eq!(*pass, KlujurVal::int(2));
    } else {
        panic!("Expected a map result");
    }
}

#[test]
fn test_multiple_namespaces() {
    let env = new_env_with_stdlib();
    let result = eval_all(
        r#"
        (require '[klujur.test :refer [deftest is]])

        ;; Define tests in user namespace
        (deftest user-test (is (= 1 1)))

        ;; Switch to another namespace and define tests there
        (ns other.ns (:require [klujur.test :refer [deftest is]]))
        (deftest other-test (is (= 2 2)))

        ;; Run all tests
        (klujur.test/run-all-tests)
        "#,
        &env,
    )
    .unwrap();

    if let KlujurVal::Map(m, _) = result {
        let pass = m
            .get(&KlujurVal::keyword(klujur_core::Keyword::new("pass")))
            .unwrap();
        // Should have 2 tests passing (one from each namespace)
        assert_eq!(*pass, KlujurVal::int(2));
    } else {
        panic!("Expected a map result");
    }
}
