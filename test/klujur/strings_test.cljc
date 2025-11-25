;; strings_test.cljc - Tests for Klujur string operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.strings-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; String Construction
;; =============================================================================

(deftest str-test
  (testing "str with no args" (is (= "" (str))))
  (testing "str with single arg"
    (is (= "hello" (str "hello")))
    (is (= "42" (str 42)))
    (is (= ":foo" (str :foo))))
  (testing "str with multiple args"
    (is (= "hello world" (str "hello" " " "world")))
    (is (= "foo123bar" (str "foo" 123 "bar"))))
  (testing "str with nil"
    (is (= "" (str nil)))
    (is (= "ab" (str "a" nil "b")))))

(deftest subs-test
  (testing "subs with start" (is (= "lo" (subs "hello" 3))))
  (testing "subs with start and end" (is (= "ell" (subs "hello" 1 4))))
  (testing "subs empty" (is (= "" (subs "hello" 5)))))

;; =============================================================================
;; Case Conversion
;; =============================================================================

(deftest upper-case-test
  (testing "upper-case"
    (is (= "HELLO" (upper-case "hello")))
    (is (= "HELLO WORLD" (upper-case "Hello World")))
    (is (= "" (upper-case "")))))

(deftest lower-case-test
  (testing "lower-case"
    (is (= "hello" (lower-case "HELLO")))
    (is (= "hello world" (lower-case "Hello World")))
    (is (= "" (lower-case "")))))

(deftest capitalize-test
  (testing "capitalize"
    (is (= "Hello" (capitalize "hello")))
    (is (= "Hello world" (capitalize "hELLO wORLD")))
    (is (= "" (capitalize "")))))

;; =============================================================================
;; Trimming
;; =============================================================================

(deftest trim-test
  (testing "trim"
    (is (= "hello" (trim "  hello  ")))
    (is (= "hello" (trim "hello")))
    (is (= "" (trim "   ")))))

(deftest triml-test
  (testing "triml"
    (is (= "hello  " (triml "  hello  ")))
    (is (= "hello" (triml "hello")))))

(deftest trimr-test
  (testing "trimr"
    (is (= "  hello" (trimr "  hello  ")))
    (is (= "hello" (trimr "hello")))))

;; =============================================================================
;; Split and Join
;; =============================================================================

(deftest split-test
  (testing "split with string delimiter"
    (is (= ["a" "b" "c"] (split "a,b,c" ","))))
  (testing "split with no matches" (is (= ["abc"] (split "abc" ","))))
  (testing "split empty string" (is (= [""] (split "" ",")))))

(deftest join-test
  (testing "join with separator" (is (= "a,b,c" (join "," ["a" "b" "c"]))))
  (testing "join without separator" (is (= "abc" (join ["a" "b" "c"]))))
  (testing "join empty" (is (= "" (join "," [])))))

;; =============================================================================
;; Replace
;; =============================================================================

(deftest replace-test
  (testing "replace all occurrences" (is (= "bbb" (replace "aaa" "a" "b"))))
  (testing "replace no match" (is (= "hello" (replace "hello" "x" "y")))))

(deftest replace-first-test
  (testing "replace-first" (is (= "baa" (replace-first "aaa" "a" "b"))))
  (testing "replace-first no match"
    (is (= "hello" (replace-first "hello" "x" "y")))))

;; =============================================================================
;; Predicates
;; =============================================================================

(deftest blank-test
  (testing "blank?"
    (is (true? (blank? nil)))
    (is (true? (blank? "")))
    (is (true? (blank? "   ")))
    (is (false? (blank? "hello")))
    (is (false? (blank? "  x  ")))))

(deftest starts-with-test
  (testing "starts-with?"
    (is (true? (starts-with? "hello" "hel")))
    (is (true? (starts-with? "hello" "")))
    (is (false? (starts-with? "hello" "ello")))))

(deftest ends-with-test
  (testing "ends-with?"
    (is (true? (ends-with? "hello" "llo")))
    (is (true? (ends-with? "hello" "")))
    (is (false? (ends-with? "hello" "hel")))))

(deftest includes-test
  (testing "includes?"
    (is (true? (includes? "hello" "ell")))
    (is (true? (includes? "hello" "")))
    (is (false? (includes? "hello" "xyz")))))

(run-all-tests)
