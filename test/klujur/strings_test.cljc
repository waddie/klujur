;; strings_test.cljc - Tests for Klujur string operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.strings-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; String Construction
;; =============================================================================

(deftest str-test
  (testing "str with no args" (is (= "" (eval* "(str)"))))
  (testing "str with single arg"
    (is (= "hello" (eval* "(str \"hello\")")))
    (is (= "42" (eval* "(str 42)")))
    (is (= ":foo" (eval* "(str :foo)"))))
  (testing "str with multiple args"
    (is (= "hello world" (eval* "(str \"hello\" \" \" \"world\")")))
    (is (= "foo123bar" (eval* "(str \"foo\" 123 \"bar\")"))))
  (testing "str with nil"
    (is (= "" (eval* "(str nil)")))
    (is (= "ab" (eval* "(str \"a\" nil \"b\")")))))

(deftest subs-test
  (testing "subs with start" (is (= "lo" (eval* "(subs \"hello\" 3)"))))
  (testing "subs with start and end"
    (is (= "ell" (eval* "(subs \"hello\" 1 4)"))))
  (testing "subs empty" (is (= "" (eval* "(subs \"hello\" 5)")))))

;; =============================================================================
;; Case Conversion
;; =============================================================================

(deftest upper-case-test
  (testing "upper-case"
    (is (= "HELLO" (eval* "(upper-case \"hello\")")))
    (is (= "HELLO WORLD" (eval* "(upper-case \"Hello World\")")))
    (is (= "" (eval* "(upper-case \"\")")))))

(deftest lower-case-test
  (testing "lower-case"
    (is (= "hello" (eval* "(lower-case \"HELLO\")")))
    (is (= "hello world" (eval* "(lower-case \"Hello World\")")))
    (is (= "" (eval* "(lower-case \"\")")))))

(deftest capitalize-test
  (testing "capitalize"
    (is (= "Hello" (eval* "(capitalize \"hello\")")))
    (is (= "Hello world" (eval* "(capitalize \"hELLO wORLD\")")))
    (is (= "" (eval* "(capitalize \"\")")))))

;; =============================================================================
;; Trimming
;; =============================================================================

(deftest trim-test
  (testing "trim"
    (is (= "hello" (eval* "(trim \"  hello  \")")))
    (is (= "hello" (eval* "(trim \"hello\")")))
    (is (= "" (eval* "(trim \"   \")")))))

(deftest triml-test
  (testing "triml"
    (is (= "hello  " (eval* "(triml \"  hello  \")")))
    (is (= "hello" (eval* "(triml \"hello\")")))))

(deftest trimr-test
  (testing "trimr"
    (is (= "  hello" (eval* "(trimr \"  hello  \")")))
    (is (= "hello" (eval* "(trimr \"hello\")")))))

;; =============================================================================
;; Split and Join
;; =============================================================================

(deftest split-test
  (testing "split with string delimiter"
    (is (= ["a" "b" "c"] (eval* "(split \"a,b,c\" \",\")"))))
  (testing "split with no matches"
    (is (= ["abc"] (eval* "(split \"abc\" \",\")"))))
  (testing "split empty string" (is (= [""] (eval* "(split \"\" \",\")")))))

(deftest join-test
  (testing "join with separator"
    (is (= "a,b,c" (eval* "(join \",\" [\"a\" \"b\" \"c\"])"))))
  (testing "join without separator"
    (is (= "abc" (eval* "(join [\"a\" \"b\" \"c\"])"))))
  (testing "join empty" (is (= "" (eval* "(join \",\" [])")))))

;; =============================================================================
;; Replace
;; =============================================================================

(deftest replace-test
  (testing "replace all occurrences"
    (is (= "bbb" (eval* "(replace \"aaa\" \"a\" \"b\")"))))
  (testing "replace no match"
    (is (= "hello" (eval* "(replace \"hello\" \"x\" \"y\")")))))

(deftest replace-first-test
  (testing "replace-first"
    (is (= "baa" (eval* "(replace-first \"aaa\" \"a\" \"b\")"))))
  (testing "replace-first no match"
    (is (= "hello" (eval* "(replace-first \"hello\" \"x\" \"y\")")))))

;; =============================================================================
;; Predicates
;; =============================================================================

(deftest blank-test
  (testing "blank?"
    (is (true? (eval* "(blank? nil)")))
    (is (true? (eval* "(blank? \"\")")))
    (is (true? (eval* "(blank? \"   \")")))
    (is (false? (eval* "(blank? \"hello\")")))
    (is (false? (eval* "(blank? \"  x  \")")))))

(deftest starts-with-test
  (testing "starts-with?"
    (is (true? (eval* "(starts-with? \"hello\" \"hel\")")))
    (is (true? (eval* "(starts-with? \"hello\" \"\")")))
    (is (false? (eval* "(starts-with? \"hello\" \"ello\")")))))

(deftest ends-with-test
  (testing "ends-with?"
    (is (true? (eval* "(ends-with? \"hello\" \"llo\")")))
    (is (true? (eval* "(ends-with? \"hello\" \"\")")))
    (is (false? (eval* "(ends-with? \"hello\" \"hel\")")))))

(deftest includes-test
  (testing "includes?"
    (is (true? (eval* "(includes? \"hello\" \"ell\")")))
    (is (true? (eval* "(includes? \"hello\" \"\")")))
    (is (false? (eval* "(includes? \"hello\" \"xyz\")")))))
