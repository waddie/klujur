;; special_forms_test.cljc - Tests for Klujur special forms
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.special-forms-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; Helper function for short-circuit tests
(defn exception [] (throw (ex-info "Should not be called" {})))

;; =============================================================================
;; if
;; =============================================================================

(deftest if-basic-test
  (testing "if with true condition"
    (is (= 1 (if true 1 2)))
    (is (= 1 (if true 1))))
  (testing "if with false condition"
    (is (= 2 (if false 1 2)))
    (is (nil? (if false 1))))
  (testing "if with nil condition"
    (is (= 2 (if nil 1 2)))
    (is (nil? (if nil 1)))))

(deftest if-truthiness-test
  (testing "everything except nil and false is truthy"
    ;; From Clojure's logic.clj - zero/empty values are truthy
    (is (= :t (if 0 :t :f)))        ; zero is truthy
    (is (= :t (if -1 :t :f)))       ; negative numbers are truthy
    (is (= :t (if 0.0 :t :f)))      ; zero float is truthy
    (is (= :t (if "" :t :f)))       ; empty string is truthy
    (is (= :t (if '() :t :f)))      ; empty list is truthy
    (is (= :t (if [] :t :f)))       ; empty vector is truthy
    (is (= :t (if {} :t :f)))       ; empty map is truthy
    (is (= :t (if #{} :t :f)))      ; empty set is truthy
    (is (= :t (if :keyword :t :f))) ; keywords are truthy
    (is (= :t (if 'symbol :t :f))))) ; symbols are truthy

(deftest if-short-circuit-test
  (testing "if does not evaluate else branch when true"
    (is (= 1 (if true 1 (exception)))))
  (testing "if does not evaluate then branch when false"
    (is (= 2 (if false (exception) 2)))))

(deftest if-arity-test
  (testing "if with too few arguments"
    ;; (if true) should error - missing then branch
    (is (thrown? Exception (eval '(if true)))))
  (testing "if with too many arguments"
    ;; (if true 1 2 3) should error
    (is (thrown? Exception (eval '(if true 1 2 3))))))

(deftest if-nested-test
  (testing "nested if expressions"
    (is (= :a (if true (if true :a :b) :c)))
    (is (= :b (if true (if false :a :b) :c)))
    (is (= :c (if false (if true :a :b) :c)))))

;; =============================================================================
;; do
;; =============================================================================

(deftest do-basic-test
  (testing "empty do returns nil" (is (nil? (do))))
  (testing "do with single expression" (is (= 1 (do 1))))
  (testing "do returns last expression" (is (= 3 (do 1 2 3)))))

(deftest do-side-effects-test
  (testing "do evaluates all expressions"
    ;; Side effects from all expressions should occur. This test requires
    ;; atom support, so for now test with nested do
    (is (= 3 (do (do 1) (do 2) 3)))))

(deftest do-with-definitions-test
  (testing "do with def" (is (= 42 (do (def x 42) x))))
  (testing "multiple defs in do" (is (= 3 (do (def a 1) (def b 2) (+ a b))))))

;; =============================================================================
;; let
;; =============================================================================

(deftest let-basic-test
  (testing "empty let"
    (is (nil? (let [])))
    (is (= 1
           (let []
             1))))
  (testing "single binding"
    (is (= 1
           (let [x 1]
             x))))
  (testing "multiple bindings"
    (is (= 3
           (let [x 1
                 y 2]
             (+ x y))))))

(deftest let-sequential-binding-test
  (testing "bindings can reference earlier bindings"
    (is (= 3
           (let [x 1
                 y (+ x 2)]
             y)))
    (is (= 6
           (let [a 1
                 b (+ a 1)
                 c (+ b 1)
                 d (+ c 1)
                 e (+ d 1)
                 f (+ e 1)]
             f)))))

(deftest let-shadowing-test
  (testing "let shadows outer bindings"
    (is (= 2
           (let [x 1]
             (let [x 2]
               x)))))
  (testing "outer binding restored after inner let"
    (is (= 1
           (let [x 1]
             (let [x 2]
               x)
             x)))))

(deftest let-multiple-body-expressions-test
  (testing "let evaluates all body expressions"
    (is (= 3
           (let [x 1]
             1
             2
             3)))
    (is (= :last
           (let [x 1]
             :first
             :middle
             :last)))))

(deftest let-nested-test
  (testing "nested let expressions"
    (is (= 3
           (let [x 1]
             (let [y 2]
               (+ x y))))))
  (testing "deeply nested lets"
    (is (= 6
           (let [a 1]
             (let [b 2]
               (let [c 3]
                 (+ a b c))))))))

(deftest let*-test
  (testing "let* is the primitive form"
    (is (= 1 (let* [x 1] x)))
    (is (= 3 (let* [x 1 y 2] (+ x y))))))

;; =============================================================================
;; quote
;; =============================================================================

(deftest quote-basic-test
  (testing "quote symbols" (is (= 'foo (quote foo))) (is (= 'foo 'foo)))
  (testing "quote numbers (self-evaluating)"
    (is (= 42 (quote 42)))
    (is (= 42 '42)))
  (testing "quote strings (self-evaluating)"
    (is (= "hello" (quote "hello")))
    (is (= "hello" '"hello"))))

(deftest quote-collections-test
  (testing "quote lists"
    (is (= '(1 2 3) '(1 2 3)))
    (is (= '(a b c) '(a b c)))
    (is (= '(+ 1 2) '(+ 1 2)))) ; + is not called
  (testing "quote vectors" (is (= '[1 2 3] '[1 2 3])))
  (testing "quote maps" (is (= '{:a 1} '{:a 1})))
  (testing "quote sets" (is (= '#{1 2} '#{1 2}))))

(deftest quote-nested-test
  (testing "nested quote"
    (is (= '(quote x) ''x))
    (is (= '(quote (1 2 3)) ''(1 2 3)))))

(deftest quote-arity-test
  (testing "quote with wrong arity"
    ;; (quote) or (quote a b) should error
    (is (thrown? Exception (eval '(quote))))
    (is (thrown? Exception (eval '(quote a b))))))

;; =============================================================================
;; fn
;; =============================================================================

(deftest fn-basic-test
  (testing "fn creates a function" (is (fn? (fn [] 1))) (is (fn? (fn [x] x))))
  (testing "fn can be called"
    (is (= 1 ((fn [] 1))))
    (is (= 42 ((fn [x] x) 42)))))

(deftest fn-with-parameters-test
  (testing "single parameter" (is (= 2 ((fn [x] (+ x 1)) 1))))
  (testing "multiple parameters" (is (= 6 ((fn [x y z] (+ x y z)) 1 2 3)))))

(deftest fn-with-body-test
  (testing "multiple body expressions" (is (= 3 ((fn [] 1 2 3)))))
  (testing "body can reference parameters"
    (is (= 10 ((fn [x] (def y 5) (+ x y)) 5)))))

(deftest fn-named-test
  (testing "named fn for recursion"
    (is (= 120 ((fn fact [n] (if (= n 0) 1 (* n (fact (- n 1))))) 5)))))

(deftest fn*-test
  (testing "fn* is the primitive form"
    (is (fn? (fn* [] 1)))
    (is (= 1 ((fn* [] 1))))))

;; =============================================================================
;; def
;; =============================================================================

(deftest def-basic-test
  (testing "def creates a var"
    (is (= 42 (do (def x 42) x)))
    (is (= :value (do (def my-var :value) my-var)))))

;; Klujur follows Clojure semantics: (def x) creates an unbound var
(deftest def-without-value-test
  (testing "def without value creates unbound var"
    ;; Accessing an unbound var throws an exception
    (is (thrown? Exception (do (def unbound-test-x) unbound-test-x)))))

(deftest def-with-docstring-test
  (testing "def with docstring"
    (is (= 42 (do (def docstring-test-x "A number" 42) docstring-test-x)))))

(deftest def-redefinition-test
  (testing "def can redefine" (is (= 2 (do (def x 1) (def x 2) x)))))

(deftest def-returns-var-test
  (testing "def returns the var"
    ;; In Clojure, (def x 1) returns #'user/x
    ;; Klujur may return the var or the value
    (is (var? (def test-var-for-return 1)))))

;; =============================================================================
;; Interaction between special forms
;; =============================================================================

(deftest special-forms-interaction-test
  (testing "if inside let"
    (is (= :yes
           (let [x 1]
             (if (= x 1) :yes :no)))))
  (testing "let inside if"
    (is (= 42
           (if true
             (let [x 42]
               x)
             0))))
  (testing "fn inside let"
    (is (= 3
           (let [f (fn [x] (+ x 1))]
             (f 2)))))
  (testing "let inside fn"
    (is (= 3
           ((fn [x]
              (let [y 2]
                (+ x y)))
            1))))
  (testing "def inside do inside let"
    (is (= 42
           (let [result (do (def inner 42) inner)]
             result)))))

(run-all-tests)
