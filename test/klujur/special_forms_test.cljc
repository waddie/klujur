;; special_forms_test.cljc - Tests for Klujur special forms
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.special-forms-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval* exception]]))

;; =============================================================================
;; if
;; =============================================================================

(deftest if-basic-test
  (testing "if with true condition"
    (is (= 1 (eval* "(if true 1 2)")))
    (is (= 1 (eval* "(if true 1)"))))
  (testing "if with false condition"
    (is (= 2 (eval* "(if false 1 2)")))
    (is (nil? (eval* "(if false 1)"))))
  (testing "if with nil condition"
    (is (= 2 (eval* "(if nil 1 2)")))
    (is (nil? (eval* "(if nil 1)")))))

(deftest if-truthiness-test
  (testing "everything except nil and false is truthy"
    ;; From Clojure's logic.clj - zero/empty values are truthy
    (are [x] (= :t (eval* (str "(if " x " :t :f)")))
     "0"        ; zero is truthy
     "-1"       ; negative numbers are truthy
     "0.0"      ; zero float is truthy
     "\"\""     ; empty string is truthy
     "'()"      ; empty list is truthy
     "[]"       ; empty vector is truthy
     "{}"       ; empty map is truthy
     "#{}"      ; empty set is truthy
     ":keyword" ; keywords are truthy
     "'symbol")))  ; symbols are truthy

(deftest if-short-circuit-test
  (testing "if does not evaluate else branch when true"
    (is (= 1 (eval* "(if true 1 (exception))"))))
  (testing "if does not evaluate then branch when false"
    (is (= 2 (eval* "(if false (exception) 2)")))))

(deftest if-arity-test
  (testing "if with too few arguments"
    ;; (if true) should error - missing then branch
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(if true)"))))
  (testing "if with too many arguments"
    ;; (if true 1 2 3) should error
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(if true 1 2 3)")))))

(deftest if-nested-test
  (testing "nested if expressions"
    (is (= :a (eval* "(if true (if true :a :b) :c)")))
    (is (= :b (eval* "(if true (if false :a :b) :c)")))
    (is (= :c (eval* "(if false (if true :a :b) :c)")))))

;; =============================================================================
;; do
;; =============================================================================

(deftest do-basic-test
  (testing "empty do returns nil" (is (nil? (eval* "(do)"))))
  (testing "do with single expression" (is (= 1 (eval* "(do 1)"))))
  (testing "do returns last expression" (is (= 3 (eval* "(do 1 2 3)")))))

(deftest do-side-effects-test
  (testing "do evaluates all expressions"
    ;; Side effects from all expressions should occur. This test requires
    ;; atom support, so for now test with nested do
    (is (= 3 (eval* "(do (do 1) (do 2) 3)")))))

(deftest do-with-definitions-test
  (testing "do with def" (is (= 42 (eval* "(do (def x 42) x)"))))
  (testing "multiple defs in do"
    (is (= 3 (eval* "(do (def a 1) (def b 2) (+ a b))")))))

;; =============================================================================
;; let
;; =============================================================================

(deftest let-basic-test
  (testing "empty let"
    (is (nil? (eval* "(let [])")))
    (is (= 1 (eval* "(let [] 1)"))))
  (testing "single binding" (is (= 1 (eval* "(let [x 1] x)"))))
  (testing "multiple bindings" (is (= 3 (eval* "(let [x 1 y 2] (+ x y))")))))

(deftest let-sequential-binding-test
  (testing "bindings can reference earlier bindings"
    (is (= 3 (eval* "(let [x 1 y (+ x 2)] y)")))
    (is (=
         6
         (eval*
          "(let [a 1 b (+ a 1) c (+ b 1) d (+ c 1) e (+ d 1) f (+ e 1)] f)")))))

(deftest let-shadowing-test
  (testing "let shadows outer bindings"
    (is (= 2 (eval* "(let [x 1] (let [x 2] x))"))))
  (testing "outer binding restored after inner let"
    (is (= 1 (eval* "(let [x 1] (let [x 2] x) x)")))))

(deftest let-multiple-body-expressions-test
  (testing "let evaluates all body expressions"
    (is (= 3 (eval* "(let [x 1] 1 2 3)")))
    (is (= :last (eval* "(let [x 1] :first :middle :last)")))))

(deftest let-nested-test
  (testing "nested let expressions"
    (is (= 3 (eval* "(let [x 1] (let [y 2] (+ x y)))"))))
  (testing "deeply nested lets"
    (is (= 6 (eval* "(let [a 1] (let [b 2] (let [c 3] (+ a b c))))")))))

(deftest let*-test
  (testing "let* is the primitive form"
    (is (= 1 (eval* "(let* [x 1] x)")))
    (is (= 3 (eval* "(let* [x 1 y 2] (+ x y))")))))

;; =============================================================================
;; quote
;; =============================================================================

(deftest quote-basic-test
  (testing "quote symbols"
    (is (= 'foo (eval* "(quote foo)")))
    (is (= 'foo (eval* "'foo"))))
  (testing "quote numbers (self-evaluating)"
    (is (= 42 (eval* "(quote 42)")))
    (is (= 42 (eval* "'42"))))
  (testing "quote strings (self-evaluating)"
    (is (= "hello" (eval* "(quote \"hello\")")))
    (is (= "hello" (eval* "'\"hello\"")))))

(deftest quote-collections-test
  (testing "quote lists"
    (is (= '(1 2 3) (eval* "'(1 2 3)")))
    (is (= '(a b c) (eval* "'(a b c)")))
    (is (= '(+ 1 2) (eval* "'(+ 1 2)")))) ; + is not called
  (testing "quote vectors" (is (= '[1 2 3] (eval* "'[1 2 3]"))))
  (testing "quote maps" (is (= '{:a 1} (eval* "'{:a 1}"))))
  (testing "quote sets" (is (= '#{1 2} (eval* "'#{1 2}")))))

(deftest quote-nested-test
  (testing "nested quote"
    (is (= '(quote x) (eval* "''x")))
    (is (= '(quote (1 2 3)) (eval* "''(1 2 3)")))))

(deftest quote-arity-test
  (testing "quote with wrong arity"
    ;; (quote) or (quote a b) should error
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(quote)")))
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(quote a b)")))))

;; =============================================================================
;; fn
;; =============================================================================

(deftest fn-basic-test
  (testing "fn creates a function"
    (is (fn? (eval* "(fn [] 1)")))
    (is (fn? (eval* "(fn [x] x)"))))
  (testing "fn can be called"
    (is (= 1 (eval* "((fn [] 1))")))
    (is (= 42 (eval* "((fn [x] x) 42)")))))

(deftest fn-with-parameters-test
  (testing "single parameter" (is (= 2 (eval* "((fn [x] (+ x 1)) 1)"))))
  (testing "multiple parameters"
    (is (= 6 (eval* "((fn [x y z] (+ x y z)) 1 2 3)")))))

(deftest fn-with-body-test
  (testing "multiple body expressions" (is (= 3 (eval* "((fn [] 1 2 3))"))))
  (testing "body can reference parameters"
    (is (= 10 (eval* "((fn [x] (def y 5) (+ x y)) 5)")))))

(deftest fn-named-test
  (testing "named fn for recursion"
    (is (= 120
           (eval* "((fn fact [n] (if (= n 0) 1 (* n (fact (- n 1))))) 5)")))))

(deftest fn*-test
  (testing "fn* is the primitive form"
    (is (fn? (eval* "(fn* [] 1)")))
    (is (= 1 (eval* "((fn* [] 1))")))))

;; =============================================================================
;; def
;; =============================================================================

(deftest def-basic-test
  (testing "def creates a var"
    (is (= 42 (eval* "(do (def x 42) x)")))
    (is (= :value (eval* "(do (def my-var :value) my-var)")))))

(deftest def-without-value-test
  (testing "def without value creates unbound var"
    ;; (def x) creates x but it's unbound
    ;; Accessing unbound var should error
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(do (def x) x)")))))

(deftest def-with-docstring-test
  (testing "def with docstring"
    (is (= 42 (eval* "(do (def x \"A number\" 42) x)")))))

(deftest def-redefinition-test
  (testing "def can redefine" (is (= 2 (eval* "(do (def x 1) (def x 2) x)")))))

(deftest def-returns-var-test
  (testing "def returns the var"
    ;; In Clojure, (def x 1) returns #'user/x
    ;; Klujur may return the var or the value
    (is (var? (eval* "(def x 1)")))))

;; =============================================================================
;; Interaction between special forms
;; =============================================================================

(deftest special-forms-interaction-test
  (testing "if inside let"
    (is (= :yes (eval* "(let [x 1] (if (= x 1) :yes :no))"))))
  (testing "let inside if" (is (= 42 (eval* "(if true (let [x 42] x) 0)"))))
  (testing "fn inside let"
    (is (= 3 (eval* "(let [f (fn [x] (+ x 1))] (f 2))"))))
  (testing "let inside fn"
    (is (= 3 (eval* "((fn [x] (let [y 2] (+ x y))) 1)"))))
  (testing "def inside do inside let"
    (is (= 42 (eval* "(let [result (do (def inner 42) inner)] result)")))))
