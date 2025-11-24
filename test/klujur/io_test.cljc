;; io_test.cljc - Tests for Klujur I/O operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.io-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; String Conversion (str, pr-str)
;; =============================================================================

(deftest str-basic-test
  (testing "str with no args" (is (= "" (eval* "(str)"))))
  (testing "str with single arg"
    (is (= "hello" (eval* "(str \"hello\")")))
    (is (= "42" (eval* "(str 42)")))
    (is (= "true" (eval* "(str true)")))
    (is (= "" (eval* "(str nil)"))))
  (testing "str with multiple args"
    (is (= "hello world" (eval* "(str \"hello\" \" \" \"world\")")))
    (is (= "123abc" (eval* "(str 123 \"abc\")")))))

(deftest pr-str-test
  (testing "pr-str produces readable strings"
    (is (= "\"hello\"" (eval* "(pr-str \"hello\")")))
    (is (= "42" (eval* "(pr-str 42)")))
    (is (= "nil" (eval* "(pr-str nil)")))
    (is (= ":keyword" (eval* "(pr-str :keyword)"))))
  (testing "pr-str with multiple args"
    (is (= "1 2 3" (eval* "(pr-str 1 2 3)")))))

;; =============================================================================
;; Read String (parsing Klujur code from strings)
;; =============================================================================

(deftest read-string-test
  (testing "read-string basic values"
    (is (= 42 (eval* "(read-string \"42\")")))
    (is (= "hello" (eval* "(read-string \"\\\"hello\\\"\")")))
    (is (nil? (eval* "(read-string \"nil\")")))
    (is (true? (eval* "(read-string \"true\")"))))
  (testing "read-string collections"
    (is (= [1 2 3] (eval* "(read-string \"[1 2 3]\")")))
    (is (= '(1 2 3) (eval* "(read-string \"(1 2 3)\")")))
    (is (= {:a 1} (eval* "(read-string \"{:a 1}\")"))))
  (testing "read-string symbols and keywords"
    (is (= 'foo (eval* "(read-string \"foo\")")))
    (is (= :bar (eval* "(read-string \":bar\")")))))

;; =============================================================================
;; File I/O (slurp, spit)
;; =============================================================================

(deftest slurp-spit-test
  (testing "spit writes content to file"
    (eval* "(spit \"/tmp/klujur-test.txt\" \"Hello, Klujur!\")")
    (is (= "Hello, Klujur!" (eval* "(slurp \"/tmp/klujur-test.txt\")"))))
  (testing "spit with append option"
    (eval* "(spit \"/tmp/klujur-test-append.txt\" \"Line 1\\n\")")
    (eval* "(spit \"/tmp/klujur-test-append.txt\" \"Line 2\\n\" :append true)")
    (is (= "Line 1\nLine 2\n"
           (eval* "(slurp \"/tmp/klujur-test-append.txt\")"))))
  (testing "spit overwrites by default"
    (eval* "(spit \"/tmp/klujur-test-overwrite.txt\" \"First\")")
    (eval* "(spit \"/tmp/klujur-test-overwrite.txt\" \"Second\")")
    (is (= "Second" (eval* "(slurp \"/tmp/klujur-test-overwrite.txt\")")))))

;; =============================================================================
;; String Formatting
;; =============================================================================

(deftest format-test
  (testing "format basic string interpolation"
    (is (= "hello world" (eval* "(format \"hello %s\" \"world\")")))
    (is (= "answer is 42" (eval* "(format \"answer is %s\" 42)"))))
  (testing "format with multiple arguments"
    (is (= "x=1, y=2" (eval* "(format \"x=%s, y=%s\" 1 2)"))))
  (testing "format with no arguments"
    (is (= "plain text" (eval* "(format \"plain text\")")))))

;; =============================================================================
;; Print Length Control
;; =============================================================================

(deftest print-length-test
  (testing "set-print-length! and get-print-length"
    (is (nil? (eval* "(get-print-length)")))
    (eval* "(set-print-length! 3)")
    (is (= 3 (eval* "(get-print-length)")))
    (eval* "(set-print-length! nil)")
    (is (nil? (eval* "(get-print-length)")))))

;; =============================================================================
;; Environment Variables
;; =============================================================================

(deftest getenv-test
  (testing "getenv retrieves environment variable"
    ;; PATH should exist on all systems
    (is (string? (eval* "(getenv \"PATH\")")))
    (is (not (empty? (eval* "(getenv \"PATH\")")))))
  (testing "getenv with non-existent variable"
    (is (nil? (eval* "(getenv \"KLUJUR_NONEXISTENT_VAR_12345\")")))))

(deftest setenv-test
  (testing "setenv sets environment variable"
    (eval* "(setenv \"KLUJUR_TEST_VAR\" \"test-value\")")
    (is (= "test-value" (eval* "(getenv \"KLUJUR_TEST_VAR\")"))))
  (testing "setenv overwrites existing variable"
    (eval* "(setenv \"KLUJUR_TEST_VAR\" \"first\")")
    (eval* "(setenv \"KLUJUR_TEST_VAR\" \"second\")")
    (is (= "second" (eval* "(getenv \"KLUJUR_TEST_VAR\")")))))

;; =============================================================================
;; Flush (no-op in Klujur but should not error)
;; =============================================================================

(deftest flush-test
  (testing "flush does not error" (is (nil? (eval* "(flush)")))))

;; NOTE: println, print, pr, prn are not tested here because they write to
;; stdout
;; and we don't have output capture support yet (see test_helper.cljc for
;; details).
;; These functions are tested indirectly through REPL usage and other tests.

;; NOTE: read-line is not tested here because it requires stdin interaction,
;; which is difficult to test in an automated test suite.

;; NOTE: exit is not tested here because it terminates the process.
