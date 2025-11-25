;; io_test.cljc - Tests for Klujur I/O operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.io-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]
            [klujur.io :refer [flush getenv setenv]]))

;; =============================================================================
;; String Conversion (str, pr-str)
;; =============================================================================

(deftest str-basic-test
  (testing "str with no args" (is (= "" (str))))
  (testing "str with single arg"
    (is (= "hello" (str "hello")))
    (is (= "42" (str 42)))
    (is (= "true" (str true)))
    (is (= "" (str nil))))
  (testing "str with multiple args"
    (is (= "hello world" (str "hello" " " "world")))
    (is (= "123abc" (str 123 "abc")))))

(deftest pr-str-test
  (testing "pr-str produces readable strings"
    (is (= "\"hello\"" (pr-str "hello")))
    (is (= "42" (pr-str 42)))
    (is (= "nil" (pr-str nil)))
    (is (= ":keyword" (pr-str :keyword))))
  (testing "pr-str with multiple args" (is (= "1 2 3" (pr-str 1 2 3)))))

;; =============================================================================
;; Read String (parsing Klujur code from strings)
;; =============================================================================

(deftest read-string-test
  (testing "read-string basic values"
    (is (= 42 (read-string "42")))
    (is (= "hello" (read-string "\"hello\"")))
    (is (nil? (read-string "nil")))
    (is (true? (read-string "true"))))
  (testing "read-string collections"
    (is (= [1 2 3] (read-string "[1 2 3]")))
    (is (= '(1 2 3) (read-string "(1 2 3)")))
    (is (= {:a 1} (read-string "{:a 1}"))))
  (testing "read-string symbols and keywords"
    (is (= 'foo (read-string "foo")))
    (is (= :bar (read-string ":bar")))))

;; =============================================================================
;; File I/O (slurp, spit)
;; =============================================================================

(deftest slurp-spit-test
  (testing "spit writes content to file"
    (spit "/tmp/klujur-test.txt" "Hello, Klujur!")
    (is (= "Hello, Klujur!" (slurp "/tmp/klujur-test.txt"))))
  (testing "spit with append option"
    (spit "/tmp/klujur-test-append.txt" "Line 1\n")
    ;; Klujur uses map for opts: {:append true}
    (spit "/tmp/klujur-test-append.txt" "Line 2\n" {:append true})
    (is (= "Line 1\nLine 2\n" (slurp "/tmp/klujur-test-append.txt"))))
  (testing "spit overwrites by default"
    (spit "/tmp/klujur-test-overwrite.txt" "First")
    (spit "/tmp/klujur-test-overwrite.txt" "Second")
    (is (= "Second" (slurp "/tmp/klujur-test-overwrite.txt")))))

;; =============================================================================
;; String Formatting
;; =============================================================================

(deftest format-test
  (testing "format basic string interpolation"
    (is (= "hello world" (format "hello %s" "world")))
    (is (= "answer is 42" (format "answer is %s" 42))))
  (testing "format with multiple arguments"
    (is (= "x=1, y=2" (format "x=%s, y=%s" 1 2))))
  (testing "format with no arguments"
    (is (= "plain text" (format "plain text")))))

;; =============================================================================
;; Print Length Control
;; =============================================================================

(deftest print-length-test
  (testing "set-print-length! and get-print-length"
    (is (nil? (get-print-length)))
    (set-print-length! 3)
    (is (= 3 (get-print-length)))
    (set-print-length! nil)
    (is (nil? (get-print-length)))))

;; =============================================================================
;; Environment Variables
;; =============================================================================

(deftest getenv-test
  (testing "getenv retrieves environment variable"
    ;; PATH should exist on all systems
    (is (string? (getenv "PATH")))
    (is (not (empty? (getenv "PATH")))))
  (testing "getenv with non-existent variable"
    (is (nil? (getenv "KLUJUR_NONEXISTENT_VAR_12345")))))

(deftest setenv-test
  (testing "setenv sets environment variable"
    (setenv "KLUJUR_TEST_VAR" "test-value")
    (is (= "test-value" (getenv "KLUJUR_TEST_VAR"))))
  (testing "setenv overwrites existing variable"
    (setenv "KLUJUR_TEST_VAR" "first")
    (setenv "KLUJUR_TEST_VAR" "second")
    (is (= "second" (getenv "KLUJUR_TEST_VAR")))))

;; =============================================================================
;; Flush (no-op in Klujur but should not error)
;; =============================================================================

(deftest flush-test (testing "flush does not error" (is (nil? (flush)))))

;; NOTE: println, print, pr, prn are not tested here because they write to
;; stdout and we don't have output capture support yet.
;; These functions are tested indirectly through REPL usage and other tests.

;; NOTE: read-line is not tested here because it requires stdin interaction,
;; which is difficult to test in an automated test suite.

;; NOTE: exit is not tested here because it terminates the process.

(run-all-tests)
