;; functions_test.cljc - Tests for Klujur functions
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.functions-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Basic fn
;; =============================================================================

(deftest fn-creation-test
  (testing "fn creates a function"
    (is (fn? (fn [])))
    (is (fn? (fn [x] x)))
    (is (fn? (fn [x y] (+ x y))))))

(deftest fn-invocation-test
  (testing "calling a function"
    (is (= nil ((fn []))))
    (is (= 42 ((fn [] 42))))
    (is (= 1 ((fn [x] x) 1)))
    (is (= 3 ((fn [x y] (+ x y)) 1 2)))))

(deftest fn-empty-params-test
  (testing "fn with no parameters"
    (is (= :value ((fn [] :value))))
    (is (= 42
           (let [f (fn [] 42)]
             (f))))))

(deftest fn-arity-error-test
  (testing "wrong number of arguments"
    (is (thrown? Exception ((fn [x] x)))) ; too few
    (is (thrown? Exception ((fn [x] x) 1 2))))) ; too many

;; =============================================================================
;; Named Functions
;; =============================================================================

(deftest fn-named-test
  (testing "named fn" (is (fn? (fn my-fn [] 1))) (is (= 1 ((fn my-fn [] 1))))))

(deftest fn-named-recursion-test
  (testing "named fn enables recursion"
    (is (= 120 ((fn fact [n] (if (<= n 1) 1 (* n (fact (- n 1))))) 5)))
    (is (= 55
           ((fn fib [n] (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2))))) 10)))))

;; =============================================================================
;; Rest Arguments (Variadic)
;; =============================================================================

(deftest fn-rest-args-test
  (testing "fn with rest args"
    (is (= '(1 2 3) ((fn [& xs] xs) 1 2 3)))
    (is (= nil ((fn [& xs] xs)))) ; no rest args = nil
    (is (= '(3) ((fn [a b & xs] xs) 1 2 3)))))

(deftest fn-rest-args-with-required-test
  (testing "fn with required and rest args"
    (is (= [1 '(2 3 4)] ((fn [x & xs] [x xs]) 1 2 3 4)))
    (is (= [1 2 '(3 4 5)] ((fn [x y & xs] [x y xs]) 1 2 3 4 5)))))

(deftest fn-rest-args-empty-test
  (testing "rest args with no extra arguments"
    (is (= [1 nil] ((fn [x & xs] [x xs]) 1)))
    (is (= [1 2 nil] ((fn [x y & xs] [x y xs]) 1 2)))))

;; =============================================================================
;; Multi-Arity Functions
;; =============================================================================

(deftest fn-multi-arity-test
  (testing "fn with multiple arities"
    (is (= 0 ((fn ([] 0) ([x] x) ([x y] (+ x y))))))
    (is (= 1 ((fn ([] 0) ([x] x) ([x y] (+ x y))) 1)))
    (is (= 3 ((fn ([] 0) ([x] x) ([x y] (+ x y))) 1 2)))))

(deftest fn-multi-arity-no-match-test
  (testing "multi-arity with no matching arity"
    (is (thrown? Exception ((fn ([] 0) ([x] x)) 1 2 3)))))

(deftest fn-multi-arity-with-rest-test
  (testing "multi-arity with rest args"
    (is (= 0 ((fn ([] 0) ([x] x) ([x y & zs] (+ x y (count zs)))))))
    (is (= 5 ((fn ([] 0) ([x] x) ([x y & zs] (+ x y (count zs)))) 1 2 3 4)))))

(deftest fn-multi-arity-order-independence-test
  (testing "arity order doesn't matter"
    (is (= 1 ((fn ([x y] 2) ([x] 1) ([] 0)) :a)))
    (is (= 2 ((fn ([x] 1) ([x y] 2) ([] 0)) :a :b)))))

(deftest fn-multi-arity-errors-test
  (testing "fixed arity cannot exceed variadic arity"
    ;; If there's a variadic [x & xs], can't have [x y z] fixed
    (is (thrown? Exception (fn ([x y z] 1) ([x & xs] 2)))))
  (testing "cannot have multiple variadic arities"
    (is (thrown? Exception (fn ([& xs] 1) ([x & xs] 2))))))

;; =============================================================================
;; Closures
;; =============================================================================

(deftest closure-basic-test
  (testing "fn closes over lexical environment"
    (is (= 11
           (let [x 10]
             ((fn [y] (+ x y)) 1))))
    (is (= 42
           (let [a 40]
             (let [b 2]
               ((fn [] (+ a b)))))))))

(deftest closure-nested-test
  (testing "nested closures"
    (is (= 6
           (let [x 1]
             (let [y 2]
               (let [z 3]
                 ((fn [] (+ x y z))))))))))

(deftest closure-returned-test
  (testing "closure can be returned"
    (is (= 11
           (let [make-adder (fn [x] (fn [y] (+ x y)))]
             ((make-adder 10) 1))))
    (is (= 15
           (let [make-adder (fn [x] (fn [y] (+ x y)))
                 add5       (make-adder 5)]
             (add5 10))))))

(deftest closure-mutable-test
  (testing "closure over atom"
    (is (= 3
           (let [counter     (atom 0)
                 inc-counter (fn [] (swap! counter inc))]
             (inc-counter)
             (inc-counter)
             (inc-counter)
             @counter)))))

(deftest closure-shadows-test
  (testing "closure shadows outer binding"
    (is (= 5
           (let [x 10]
             ((fn [x] x) 5))))
    (is (= 10
           (let [x 10]
             ((fn [x] x) 5)
             x)))))

;; =============================================================================
;; Anonymous Function Literals (#())
;; =============================================================================

(deftest fn-literal-basic-test
  (testing "#() creates a function"
    (is (fn? #(+ 1 2)))
    (is (fn? #(identity %)))))

(deftest fn-literal-single-arg-test
  (testing "#() with single argument %"
    (is (= 2 (#(+ % 1) 1)))
    (is (= 100 (#(* % %) 10)))))

(deftest fn-literal-numbered-args-test
  (testing "#() with numbered arguments"
    (is (= 3 (#(+ %1 %2) 1 2)))
    (is (= 6 (#(+ %1 %2 %3) 1 2 3)))
    (is (= [1 2 3] (#(vector %1 %2 %3) 1 2 3)))))

(deftest fn-literal-rest-args-test
  (testing "#() with rest arguments %&"
    (is (= '(1 2 3) (#(identity %&) 1 2 3)))
    (is (= 6 (#(apply + %&) 1 2 3)))
    (is (= [1 '(2 3)] (#(vector %1 %&) 1 2 3)))))

(deftest fn-literal-no-args-test
  (testing "#() with no arguments"
    (is (= 42 (#(do 42))))
    (is (= :value (#(identity :value))))))

;; Note: nested #() test omitted - Klujur catches this at parse time
;; so it cannot be tested as a runtime exception

;; =============================================================================
;; defn
;; =============================================================================

(deftest defn-basic-test
  (testing "defn defines a function"
    (is (= 42 (do (defn answer [] 42) (answer))))
    (is (= 3 (do (defn add [x y] (+ x y)) (add 1 2))))))

(deftest defn-with-docstring-test
  (testing "defn with docstring"
    (is (= 42
           (do (defn answer "Returns the answer to everything" [] 42)
               (answer))))))

(deftest defn-multi-arity-test
  (testing "defn with multiple arities"
    (is (= [0 1 3]
           (do (defn f ([] 0) ([x] x) ([x y] (+ x y))) [(f) (f 1) (f 1 2)])))))

(deftest defn-with-rest-args-test
  (testing "defn with rest args"
    (is (= '(2 3 4) (do (defn rest-fn [x & xs] xs) (rest-fn 1 2 3 4))))))

(deftest defn-with-metadata-test
  (testing "defn with attr-map metadata"
    (is (= 42
           (do (defn answer {:doc "The answer" :private true} [] 42)
               (answer))))))

;; =============================================================================
;; Pre and Post Conditions
;; =============================================================================

(deftest fn-precondition-test
  (testing "fn with :pre condition"
    (is (= 2 ((fn [x] {:pre [(pos? x)]} x) 2)))
    (is (thrown? Exception ((fn [x] {:pre [(pos? x)]} x) -1)))))

(deftest fn-postcondition-test
  (testing "fn with :post condition"
    (is (= 2 ((fn [x] {:post [(pos? %)]} x) 2)))
    (is (thrown? Exception ((fn [x] {:post [(pos? %)]} x) -1)))))

(deftest fn-pre-and-post-test
  (testing "fn with both :pre and :post"
    (is (= 4 ((fn [x] {:pre [(pos? x)] :post [(> % x)]} (* x 2)) 2)))
    (is (thrown? Exception ((fn [x] {:pre [(pos? x)] :post [(> % x)]} x) 2)))))

;; =============================================================================
;; apply
;; =============================================================================

(deftest apply-basic-test
  (testing "apply with list"
    (is (= 6 (apply + '(1 2 3))))
    (is (= 6 (apply + [1 2 3])))))

(deftest apply-with-initial-args-test
  (testing "apply with initial arguments"
    (is (= 10 (apply + 1 2 [3 4])))
    (is (= 15 (apply + 1 2 3 [4 5])))))

(deftest apply-empty-seq-test
  (testing "apply with empty sequence"
    (is (= 0 (apply + [])))
    (is (= 3 (apply + 1 2 [])))))

;; =============================================================================
;; partial
;; =============================================================================

(deftest partial-basic-test
  (testing "partial application"
    (is (= 11 ((partial + 10) 1)))
    (is (= 6 ((partial + 1 2) 3)))))

(deftest partial-multiple-args-test
  (testing "partial with multiple remaining args"
    (is (= 15 ((partial + 1 2 3) 4 5)))
    (is (= "hello world" ((partial str "hello") " " "world")))))

;; =============================================================================
;; comp
;; =============================================================================

(deftest comp-basic-test
  (testing "function composition"
    (is (= 4 ((comp inc inc inc) 1)))
    (is (= 6 ((comp #(* % 2) inc) 2)))))  ; inc then double

(deftest comp-right-to-left-test
  (testing "comp applies right-to-left"
    ;; (comp f g h) means f(g(h(x)))
    (is (= 12 ((comp #(* % 3) #(+ % 1)) 3))) ; (+ 3 1) = 4, (* 4 3) = 12
    (is (= 10 ((comp #(+ % 1) #(* % 3)) 3))))) ; (* 3 3) = 9, (+ 9 1) = 10

(deftest comp-identity-test
  (testing "comp with no args returns identity" (is (= 42 ((comp) 42)))))

;; =============================================================================
;; juxt
;; =============================================================================

(deftest juxt-basic-test
  (testing "juxtaposition"
    (is (= [1 2 3] ((juxt first second last) [1 2 3])))
    (is (= [2 0] ((juxt inc dec) 1)))))

(deftest juxt-multiple-args-test
  (testing "juxt with multiple argument function"
    (is (= [3 -1] ((juxt + -) 1 2)))))

;; =============================================================================
;; constantly
;; =============================================================================

(deftest constantly-test
  (testing "constantly returns constant"
    (is (= 42 ((constantly 42))))
    (is (= 42 ((constantly 42) 1 2 3)))
    (is (= :x ((constantly :x) :ignored)))))

;; =============================================================================
;; identity
;; =============================================================================

(deftest identity-test
  (testing "identity returns its argument"
    (is (= 42 (identity 42)))
    (is (= :x (identity :x)))
    (is (= [1 2] (identity [1 2])))))

;; =============================================================================
;; complement
;; =============================================================================

(deftest complement-test
  (testing "complement inverts predicate"
    (is (true? ((complement even?) 1)))
    (is (false? ((complement even?) 2)))
    (is (true? ((complement nil?) 42)))
    (is (false? ((complement nil?) nil)))))

;; =============================================================================
;; letfn
;; =============================================================================

(deftest letfn-basic-test
  (testing "letfn creates local functions"
    (is (= 5
           (letfn [(f [x] (+ x 1))]
             (f 4))))
    (is (= 42
           (letfn [(answer [] 42)]
             (answer))))))

(deftest letfn-multiple-functions-test
  (testing "letfn with multiple functions"
    (is (= 7
           (letfn [(f [x] (+ x 1)) (g [x] (* x 2))]
             (f (g 3)))))))

(deftest letfn-mutual-recursion-test
  (testing "letfn enables mutual recursion"
    (is (true? (letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                       (odd? [n] (if (zero? n) false (even? (dec n))))]
                 (even? 10))))
    (is (false? (letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                        (odd? [n] (if (zero? n) false (even? (dec n))))]
                  (even? 11))))
    (is (true? (letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
                       (odd? [n] (if (zero? n) false (even? (dec n))))]
                 (odd? 7))))))

(run-all-tests)
