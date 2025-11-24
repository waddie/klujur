;; functions_test.cljc - Tests for Klujur functions
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.functions-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Basic fn
;; =============================================================================

(deftest fn-creation-test
  (testing "fn creates a function"
    (is (fn? (eval* "(fn [])")))
    (is (fn? (eval* "(fn [x] x)")))
    (is (fn? (eval* "(fn [x y] (+ x y))")))))

(deftest fn-invocation-test
  (testing "calling a function"
    (is (= nil (eval* "((fn []))")))
    (is (= 42 (eval* "((fn [] 42))")))
    (is (= 1 (eval* "((fn [x] x) 1)")))
    (is (= 3 (eval* "((fn [x y] (+ x y)) 1 2)")))))

(deftest fn-empty-params-test
  (testing "fn with no parameters"
    (is (= :value (eval* "((fn [] :value))")))
    (is (= 42 (eval* "(let [f (fn [] 42)] (f))")))))

(deftest fn-arity-error-test
  (testing "wrong number of arguments"
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "((fn [x] x))"))) ; too few
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "((fn [x] x) 1 2)")))))     ; too many

;; =============================================================================
;; Named Functions
;; =============================================================================

(deftest fn-named-test
  (testing "named fn"
    (is (fn? (eval* "(fn my-fn [] 1)")))
    (is (= 1 (eval* "((fn my-fn [] 1))")))))

(deftest fn-named-recursion-test
  (testing "named fn enables recursion"
    (is
     (=
      120
      (eval*
       "((fn fact [n]
                          (if (<= n 1)
                            1
                            (* n (fact (- n 1)))))
                        5)")))
    (is
     (=
      55
      (eval*
       "((fn fib [n]
                         (if (<= n 1)
                           n
                           (+ (fib (- n 1)) (fib (- n 2)))))
                       10)")))))

;; =============================================================================
;; Rest Arguments (Variadic)
;; =============================================================================

(deftest fn-rest-args-test
  (testing "fn with rest args"
    (is (= '(1 2 3) (eval* "((fn [& xs] xs) 1 2 3)")))
    (is (= nil (eval* "((fn [& xs] xs))"))) ; no rest args = nil
    (is (= '(3) (eval* "((fn [a b & xs] xs) 1 2 3)")))))

(deftest fn-rest-args-with-required-test
  (testing "fn with required and rest args"
    (is (= [1 '(2 3 4)] (eval* "((fn [x & xs] [x xs]) 1 2 3 4)")))
    (is (= [1 2 '(3 4 5)] (eval* "((fn [x y & xs] [x y xs]) 1 2 3 4 5)")))))

(deftest fn-rest-args-empty-test
  (testing "rest args with no extra arguments"
    (is (= [1 nil] (eval* "((fn [x & xs] [x xs]) 1)")))
    (is (= [1 2 nil] (eval* "((fn [x y & xs] [x y xs]) 1 2)")))))

;; =============================================================================
;; Multi-Arity Functions
;; =============================================================================

(deftest fn-multi-arity-test
  (testing "fn with multiple arities"
    (is (= 0 (eval* "((fn ([] 0) ([x] x) ([x y] (+ x y))))")))
    (is (= 1 (eval* "((fn ([] 0) ([x] x) ([x y] (+ x y))) 1)")))
    (is (= 3 (eval* "((fn ([] 0) ([x] x) ([x y] (+ x y))) 1 2)")))))

(deftest fn-multi-arity-no-match-test
  (testing "multi-arity with no matching arity"
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "((fn ([] 0) ([x] x)) 1 2 3)")))))

(deftest fn-multi-arity-with-rest-test
  (testing "multi-arity with rest args"
    (is (= 0 (eval* "((fn ([] 0) ([x] x) ([x y & zs] (+ x y (count zs)))))")))
    (is (= 5
           (eval*
            "((fn ([] 0) ([x] x) ([x y & zs] (+ x y (count zs)))) 1 2 3 4)")))))

(deftest fn-multi-arity-order-independence-test
  (testing "arity order doesn't matter"
    (is (= 1 (eval* "((fn ([x y] 2) ([x] 1) ([] 0)) :a)")))
    (is (= 2 (eval* "((fn ([x] 1) ([x y] 2) ([] 0)) :a :b)")))))

(deftest fn-multi-arity-errors-test
  (testing "fixed arity cannot exceed variadic arity"
    ;; If there's a variadic [x & xs], can't have [x y z] fixed
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(fn ([x y z] 1) ([x & xs] 2))"))))
  (testing "cannot have multiple variadic arities"
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(fn ([& xs] 1) ([x & xs] 2))")))))

;; =============================================================================
;; Closures
;; =============================================================================

(deftest closure-basic-test
  (testing "fn closes over lexical environment"
    (is (= 11 (eval* "(let [x 10] ((fn [y] (+ x y)) 1))")))
    (is (= 42 (eval* "(let [a 40] (let [b 2] ((fn [] (+ a b)))))")))))

(deftest closure-nested-test
  (testing "nested closures"
    (is
     (=
      6
      (eval*
       "(let [x 1]
                       (let [y 2]
                         (let [z 3]
                           ((fn [] (+ x y z))))))")))))

(deftest closure-returned-test
  (testing "closure can be returned"
    (is
     (=
      11
      (eval*
       "(let [make-adder (fn [x] (fn [y] (+ x y)))]
                        ((make-adder 10) 1))")))
    (is
     (=
      15
      (eval*
       "(let [make-adder (fn [x] (fn [y] (+ x y)))
                           add5 (make-adder 5)]
                        (add5 10))")))))

(deftest closure-mutable-test
  (testing "closure over atom"
    (is
     (=
      3
      (eval*
       "(let [counter (atom 0)
                          inc-counter (fn [] (swap! counter inc))]
                       (inc-counter)
                       (inc-counter)
                       (inc-counter)
                       @counter)")))))

(deftest closure-shadows-test
  (testing "closure shadows outer binding"
    (is (= 5 (eval* "(let [x 10]
                       ((fn [x] x) 5))")))
    (is
     (=
      10
      (eval*
       "(let [x 10]
                        ((fn [x] x) 5)
                        x)")))))

;; =============================================================================
;; Anonymous Function Literals (#())
;; =============================================================================

(deftest fn-literal-basic-test
  (testing "#() creates a function"
    (is (fn? (eval* "#(+ 1 2)")))
    (is (fn? (eval* "#(identity %)")))))

(deftest fn-literal-single-arg-test
  (testing "#() with single argument %"
    (is (= 2 (eval* "(#(+ % 1) 1)")))
    (is (= 100 (eval* "(#(* % %) 10)")))))

(deftest fn-literal-numbered-args-test
  (testing "#() with numbered arguments"
    (is (= 3 (eval* "(#(+ %1 %2) 1 2)")))
    (is (= 6 (eval* "(#(+ %1 %2 %3) 1 2 3)")))
    (is (= [1 2 3] (eval* "(#(vector %1 %2 %3) 1 2 3)")))))

(deftest fn-literal-rest-args-test
  (testing "#() with rest arguments %&"
    (is (= '(1 2 3) (eval* "(#(identity %&) 1 2 3)")))
    (is (= 6 (eval* "(#(apply + %&) 1 2 3)")))
    (is (= [1 '(2 3)] (eval* "(#(vector %1 %&) 1 2 3)")))))

(deftest fn-literal-no-args-test
  (testing "#() with no arguments"
    (is (= 42 (eval* "(#(do 42))")))
    (is (= :value (eval* "(#(identity :value))")))))

(deftest fn-literal-nested-test
  (testing "nested #() is not allowed"
    ;; #(#(+ %)) is invalid - can't nest fn literals
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "#(#(+ %))")))))

;; =============================================================================
;; defn
;; =============================================================================

(deftest defn-basic-test
  (testing "defn defines a function"
    (is (= 42 (eval* "(do (defn answer [] 42) (answer))")))
    (is (= 3 (eval* "(do (defn add [x y] (+ x y)) (add 1 2))")))))

(deftest defn-with-docstring-test
  (testing "defn with docstring"
    (is
     (=
      42
      (eval*
       "(do (defn answer
                            \"Returns the answer to everything\"
                            [] 42)
                         (answer))")))))

(deftest defn-multi-arity-test
  (testing "defn with multiple arities"
    (is
     (=
      [0 1 3]
      (eval*
       "(do (defn f
                         ([] 0)
                         ([x] x)
                         ([x y] (+ x y)))
                       [(f) (f 1) (f 1 2)])")))))

(deftest defn-with-rest-args-test
  (testing "defn with rest args"
    (is
     (=
      '(2 3 4)
      (eval*
       "(do (defn rest-fn [x & xs] xs)
                       (rest-fn 1 2 3 4))")))))

(deftest defn-with-metadata-test
  (testing "defn with attr-map metadata"
    (is
     (=
      42
      (eval*
       "(do (defn answer
                            {:doc \"The answer\"
                             :private true}
                            [] 42)
                         (answer))")))))

;; =============================================================================
;; Pre and Post Conditions
;; =============================================================================

(deftest fn-precondition-test
  (testing "fn with :pre condition"
    (is (= 2 (eval* "((fn [x] {:pre [(pos? x)]} x) 2)")))
    (is (thrown? #?(:clj AssertionError
                    :cljs js/Error)
                 (eval* "((fn [x] {:pre [(pos? x)]} x) -1)")))))

(deftest fn-postcondition-test
  (testing "fn with :post condition"
    (is (= 2 (eval* "((fn [x] {:post [(pos? %)]} x) 2)")))
    (is (thrown? #?(:clj AssertionError
                    :cljs js/Error)
                 (eval* "((fn [x] {:post [(pos? %)]} x) -1)")))))

(deftest fn-pre-and-post-test
  (testing "fn with both :pre and :post"
    (is (= 4 (eval* "((fn [x] {:pre [(pos? x)] :post [(> % x)]} (* x 2)) 2)")))
    (is (thrown? #?(:clj AssertionError
                    :cljs js/Error)
                 (eval* "((fn [x] {:pre [(pos? x)] :post [(> % x)]} x) 2)")))))

;; =============================================================================
;; apply
;; =============================================================================

(deftest apply-basic-test
  (testing "apply with list"
    (is (= 6 (eval* "(apply + '(1 2 3))")))
    (is (= 6 (eval* "(apply + [1 2 3])")))))

(deftest apply-with-initial-args-test
  (testing "apply with initial arguments"
    (is (= 10 (eval* "(apply + 1 2 [3 4])")))
    (is (= 15 (eval* "(apply + 1 2 3 [4 5])")))))

(deftest apply-empty-seq-test
  (testing "apply with empty sequence"
    (is (= 0 (eval* "(apply + [])")))
    (is (= 3 (eval* "(apply + 1 2 [])")))))

;; =============================================================================
;; partial
;; =============================================================================

(deftest partial-basic-test
  (testing "partial application"
    (is (= 11 (eval* "((partial + 10) 1)")))
    (is (= 6 (eval* "((partial + 1 2) 3)")))))

(deftest partial-multiple-args-test
  (testing "partial with multiple remaining args"
    (is (= 15 (eval* "((partial + 1 2 3) 4 5)")))
    (is (= "hello world" (eval* "((partial str \"hello\") \" \" \"world\")")))))

;; =============================================================================
;; comp
;; =============================================================================

(deftest comp-basic-test
  (testing "function composition"
    (is (= 4 (eval* "((comp inc inc inc) 1)")))
    (is (= 6 (eval* "((comp #(* % 2) inc) 2)")))))  ; inc then double

(deftest comp-right-to-left-test
  (testing "comp applies right-to-left"
    ;; (comp f g h) means f(g(h(x)))
    (is (= 12 (eval* "((comp #(* % 3) #(+ % 1)) 3)"))) ; (+ 3 1) = 4, (* 4
                                                       ; 3) = 12
    (is (= 10 (eval* "((comp #(+ % 1) #(* % 3)) 3)"))))) ; (* 3 3) = 9, (+ 9 1) = 10

(deftest comp-identity-test
  (testing "comp with no args returns identity"
    (is (= 42 (eval* "((comp) 42)")))))

;; =============================================================================
;; juxt
;; =============================================================================

(deftest juxt-basic-test
  (testing "juxtaposition"
    (is (= [1 2 3] (eval* "((juxt first second last) [1 2 3])")))
    (is (= [2 0] (eval* "((juxt inc dec) 1)")))))

(deftest juxt-multiple-args-test
  (testing "juxt with multiple argument function"
    (is (= [3 -1] (eval* "((juxt + -) 1 2)")))))

;; =============================================================================
;; constantly
;; =============================================================================

(deftest constantly-test
  (testing "constantly returns constant"
    (is (= 42 (eval* "((constantly 42))")))
    (is (= 42 (eval* "((constantly 42) 1 2 3)")))
    (is (= :x (eval* "((constantly :x) :ignored)")))))

;; =============================================================================
;; identity
;; =============================================================================

(deftest identity-test
  (testing "identity returns its argument"
    (is (= 42 (eval* "(identity 42)")))
    (is (= :x (eval* "(identity :x)")))
    (is (= [1 2] (eval* "(identity [1 2])")))))

;; =============================================================================
;; complement
;; =============================================================================

(deftest complement-test
  (testing "complement inverts predicate"
    (is (true? (eval* "((complement even?) 1)")))
    (is (false? (eval* "((complement even?) 2)")))
    (is (true? (eval* "((complement nil?) 42)")))
    (is (false? (eval* "((complement nil?) nil)")))))

;; =============================================================================
;; letfn
;; =============================================================================

(deftest letfn-basic-test
  (testing "letfn creates local functions"
    (is (= 5 (eval* "(letfn [(f [x] (+ x 1))] (f 4))")))
    (is (= 42 (eval* "(letfn [(answer [] 42)] (answer))")))))

(deftest letfn-multiple-functions-test
  (testing "letfn with multiple functions"
    (is
     (=
      7
      (eval*
       "(letfn [(f [x] (+ x 1))
                             (g [x] (* x 2))]
                       (f (g 3)))")))))

(deftest letfn-mutual-recursion-test
  (testing "letfn enables mutual recursion"
    (is
     (true?
      (eval*
       "(letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                               (odd? [n] (if (zero? n) false (even? (dec n))))]
                         (even? 10))")))
    (is
     (false?
      (eval*
       "(letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                                (odd? [n] (if (zero? n) false (even? (dec n))))]
                          (even? 11))")))
    (is
     (true?
      (eval*
       "(letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                               (odd? [n] (if (zero? n) false (even? (dec n))))]
                         (odd? 7))")))))
