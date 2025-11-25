;; control_flow_test.cljc - Tests for Klujur control flow constructs
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.control-flow-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; Helper function for short-circuit testing
(defn exception
  []
  (throw (ex-info "Should not be reached - short-circuit evaluation failed"
                  {})))

;; =============================================================================
;; when / when-not
;; =============================================================================

(deftest when-basic-test
  (testing "when with true condition"
    (is (= 1 (when true 1)))
    (is (= 3 (when true 1 2 3)))) ; returns last
  (testing "when with false condition"
    (is (nil? (when false 1)))
    (is (nil? (when false 1 2 3))))
  (testing "when with nil condition" (is (nil? (when nil 1)))))

(deftest when-short-circuit-test
  (testing "when does not evaluate body when false"
    (is (nil? (when false (exception))))
    (is (nil? (when nil (exception))))))

(deftest when-not-basic-test
  (testing "when-not with false condition"
    (is (= 1 (when-not false 1)))
    (is (= 3 (when-not false 1 2 3))))
  (testing "when-not with true condition"
    (is (nil? (when-not true 1)))
    (is (nil? (when-not true 1 2 3))))
  (testing "when-not with nil condition" (is (= 1 (when-not nil 1)))))

(deftest when-not-short-circuit-test
  (testing "when-not does not evaluate body when true"
    (is (nil? (when-not true (exception))))))

;; =============================================================================
;; if-not
;; =============================================================================

(deftest if-not-basic-test
  (testing "if-not inverts condition"
    (is (= :else (if-not true :then :else)))
    (is (= :then (if-not false :then :else)))
    (is (= :then (if-not nil :then :else)))))

(deftest if-not-two-arg-test
  (testing "if-not without else"
    (is (nil? (if-not true :then)))
    (is (= :then (if-not false :then)))))

;; =============================================================================
;; when-let / if-let
;; =============================================================================

(deftest when-let-basic-test
  (testing "when-let with truthy binding"
    (is (= 1
           (when-let [x 1]
             x)))
    (is (= [1 2]
           (when-let [x [1 2]]
             x))))
  (testing "when-let with falsy binding"
    (is (nil? (when-let [x nil]
                x)))
    (is (nil? (when-let [x false]
                x)))))

(deftest when-let-multiple-body-test
  (testing "when-let with multiple body expressions"
    (is (= :last
           (when-let [x 1]
             :first
             :middle
             :last)))))

(deftest if-let-basic-test
  (testing "if-let with truthy binding"
    (is (= 1
           (if-let [x 1]
             x
             :else)))
    (is (= :yes
           (if-let [x true]
             :yes
             :no))))
  (testing "if-let with falsy binding"
    (is (= :else
           (if-let [x nil]
             x
             :else)))
    (is (= :else
           (if-let [x false]
             x
             :else)))))

(deftest if-let-short-circuit-test
  (testing "if-let does not evaluate else when truthy"
    (is (= 1
           (if-let [x 1]
             x
             (exception)))))
  (testing "if-let does not evaluate then when falsy"
    (is (= :else
           (if-let [x nil]
             (exception)
             :else)))))

;; =============================================================================
;; when-some / if-some
;; =============================================================================

(deftest when-some-basic-test
  (testing "when-some treats false as truthy"
    (is (= false
           (when-some [x false]
             x)))
    (is (= :yes
           (when-some [x 0]
             :yes))))
  (testing "when-some only nil is falsy"
    (is (nil? (when-some [x nil]
                x)))))

(deftest if-some-basic-test
  (testing "if-some treats false as truthy"
    (is (= false
           (if-some [x false]
             x
             :else)))
    (is (= :then
           (if-some [x false]
             :then
             :else))))
  (testing "if-some only nil is falsy"
    (is (= :else
           (if-some [x nil]
             x
             :else)))))

;; =============================================================================
;; when-first
;; =============================================================================

(deftest when-first-basic-test
  (testing "when-first with non-empty seq"
    (is (= 1
           (when-first [x [1 2 3]]
             x)))
    (is (= :a
           (when-first [x [:a :b]]
             x))))
  (testing "when-first with empty seq"
    (is (nil? (when-first [x []]
                x)))
    (is (nil? (when-first [x nil]
                x)))))

;; =============================================================================
;; cond
;; =============================================================================

(deftest cond-basic-test
  (testing "cond with matching clause"
    (is (= 1 (cond true 1)))
    (is (= :a
           (cond true :a
                 false :b))))
  (testing "cond with multiple clauses"
    (is (= :b
           (cond false :a
                 true :b
                 false :c))))
  (testing "cond with no match"
    (is (nil? (cond false 1
                    false 2)))))

(deftest cond-else-test
  (testing "cond with :else clause"
    (is (= :default
           (cond false 1
                 :else :default)))
    (is (= :default
           (cond nil :a
                 false :b
                 :else :default)))))

(deftest cond-short-circuit-test
  (testing "cond stops at first match"
    (is (= :first
           (cond true :first
                 true (exception)))))
  (testing "cond does not evaluate unmatched branches"
    (is (= :second
           (cond false (exception)
                 true :second)))))

(deftest cond-truthiness-test
  (testing "cond respects truthiness"
    ;; Everything except nil and false is truthy
    (is (= :yes (cond 0 :yes)))   ; zero is truthy
    (is (= :yes (cond '() :yes))) ; empty list is truthy
    (is (= :yes (cond [] :yes)))  ; empty vector is truthy
    (is (= :yes (cond "" :yes)))))   ; empty string is truthy

;; =============================================================================
;; condp
;; =============================================================================

(deftest condp-basic-test
  (testing "condp with matching value"
    (is (= :one (condp = 1 1 :one 2 :two 3 :three)))
    (is (= :two (condp = 2 1 :one 2 :two 3 :three)))))

(deftest condp-with-default-test
  (testing "condp with default"
    (is (= :default (condp = 4 1 :one 2 :two :default)))))

(deftest condp-no-match-test
  (testing "condp throws when no match and no default"
    (is (thrown? Exception (condp = 4 1 :one 2 :two)))))

(deftest condp-custom-predicate-test
  (testing "condp with custom predicate"
    (is (= :small (condp < 5 10 :small 20 :medium 30 :large)))
    (is (= :contains-a
           (condp contains? #{:a :b} :a :contains-a :c :contains-c)))))

(deftest condp-threading-test
  (testing "condp with :>> threading"
    ;; (condp pred expr clause :>> fn ...) threads result through fn
    (is (= 2 (condp some [1 2 3] #{2} :>> identity))))
  (testing ":>> threads predicate result through function"
    (is (= 3 (condp some [1 2 3] #{2} :>> inc))))
  (testing ":>> with multiple clauses"
    (is (= 4 (condp some [1 2 3 4] #{5} :>> inc #{4} :>> identity))))
  (testing ":>> with default clause"
    (is (= :default (condp some [1 2 3] #{5} :>> inc :default)))))

;; =============================================================================
;; case
;; =============================================================================

(deftest case-basic-test
  (testing "case with matching value"
    (is (= :one
           (case 1
             1 :one
             2 :two
             3 :three)))
    (is (= :two
           (case 2
             1 :one
             2 :two
             3 :three)))
    (is (= :three
           (case 3
             1 :one
             2 :two
             3 :three)))))

(deftest case-with-default-test
  (testing "case with default"
    (is (= :default
           (case 4
             1 :one
             2 :two
             :default)))))

(deftest case-no-match-test
  (testing "case throws when no match and no default"
    (is (thrown? Exception
                 (case 4
                   1 :one
                   2 :two)))))

(deftest case-keyword-test
  (testing "case with keywords"
    (is (= 1
           (case :a
             :a 1
             :b 2
             :c 3)))
    (is (= 2
           (case :b
             :a 1
             :b 2
             :c 3)))))

(deftest case-string-test
  (testing "case with strings"
    (is (= 1
           (case "a"
             "a" 1
             "b" 2)))
    (is (= 2
           (case "b"
             "a" 1
             "b" 2)))))

(deftest case-char-test
  (testing "case with characters"
    (is (= 1
           (case \a
             \a 1
             \b 2)))
    (is (= 2
           (case \b
             \a 1
             \b 2)))))

(deftest case-symbol-test
  (testing "case with symbols"
    (is (= 1
           (case 'a
             a 1
             b 2)))
    (is (= 2
           (case 'b
             a 1
             b 2)))))

(deftest case-nil-test
  (testing "case with nil"
    (is (= :nil-case
           (case nil
             nil :nil-case
             :default)))))

(deftest case-collection-test
  (testing "case with vectors"
    (is (= :match
           (case [1 2]
             [1 2] :match
             :no-match))))
  (testing "case with maps"
    ;; Map ordering shouldn't matter
    (is (= :match
           (case {:a 1 :b 2}
             {:b 2 :a 1} :match
             :no-match))))
  (testing "case with sets"
    ;; Set ordering shouldn't matter
    (is (= :match
           (case #{1 2 3}
             #{3 2 1} :match
             :no-match)))))

(deftest case-multiple-values-test
  (testing "case with multiple test constants"
    (is (= :small
           (case 1
             (1 2 3) :small
             (4 5 6) :medium
             :large)))
    (is (= :small
           (case 2
             (1 2 3) :small
             (4 5 6) :medium
             :large)))
    (is (= :medium
           (case 5
             (1 2 3) :small
             (4 5 6) :medium
             :large)))))

;; =============================================================================
;; loop / recur
;; =============================================================================

(deftest loop-basic-test
  (testing "loop without recur"
    (is (= 1
           (loop [x 1]
             x)))
    (is (= 3
           (loop [x 1
                  y 2]
             (+ x y))))))

(deftest loop-recur-test
  (testing "loop with recur"
    (is (= 10
           (loop [x 0]
             (if (< x 10) (recur (+ x 1)) x))))
    (is (= 55
           (loop [n   10
                  acc 0]
             (if (= n 0) acc (recur (- n 1) (+ acc n))))))))

(deftest loop-recur-builds-collection-test
  (testing "loop/recur to build a collection"
    (is (= [4 3 2 1 0]
           (loop [i    0
                  coll []]
             (if (< i 5) (recur (+ i 1) (cons i coll)) coll))))))

(deftest recur-in-fn-test
  (testing "recur in function body"
    (is (= 120
           ((fn [n]
              (loop [n   n
                     acc 1]
                (if (= n 0) acc (recur (- n 1) (* acc n)))))
            5)))))

(deftest recur-tail-position-test
  (testing "recur must be in tail position"
    ;; This should error - recur not in tail position
    (is (thrown? Exception
                 (loop [x 0]
                   (+ 1 (recur x)))))))

(deftest recur-arity-test
  (testing "recur arity must match loop bindings"
    (is (thrown? Exception
                 (loop [x 1
                        y 2]
                   (recur 3)))) ; too few
    (is (thrown? Exception
                 (loop [x 1]
                   (recur 1 2))))))  ; too many

;; =============================================================================
;; dotimes
;; =============================================================================

(deftest dotimes-basic-test
  (testing "dotimes executes n times"
    ;; dotimes always returns nil
    (is (nil? (dotimes [i 5]
                i))))
  (testing "dotimes with zero"
    (is (nil? (dotimes [i 0]
                (exception))))))

;; =============================================================================
;; while
;; =============================================================================

(deftest while-basic-test
  (testing "while loop"
    ;; Need atom support for proper while test
    ;; This tests that while returns nil
    (is (nil? (let [x (atom 0)]
                (while (< @x 5) (swap! x inc)))))))

;; =============================================================================
;; doseq
;; =============================================================================

(deftest doseq-basic-test
  (testing "doseq iterates over collection"
    ;; doseq always returns nil
    (is (nil? (doseq [x [1 2 3]]
                x))))
  (testing "doseq with empty collection"
    (is (nil? (doseq [x []]
                (exception))))))

(deftest doseq-multiple-bindings-test
  (testing "doseq with multiple bindings (cartesian product)"
    (is (nil? (doseq [x [1 2]
                      y [:a :b]]
                [x y])))))

;; =============================================================================
;; for (list comprehension)
;; =============================================================================

(deftest for-basic-test
  (testing "for creates a lazy seq"
    (is (= '(1 2 3)
           (for [x [1 2 3]]
             x)))
    (is (= '(2 4 6)
           (for [x [1 2 3]]
             (* x 2))))))

(deftest for-multiple-bindings-test
  (testing "for with multiple bindings"
    (is (= '([1 :a] [1 :b] [2 :a] [2 :b])
           (for [x [1 2]
                 y [:a :b]]
             [x y])))))

(deftest for-with-when-test
  (testing "for with :when filter"
    (is (= '(2 4)
           (for [x     [1 2 3 4]
                 :when (even? x)]
             x)))))

(deftest for-with-let-test
  (testing "for with :let binding"
    (is (= '(2 4 6)
           (for [x    [1 2 3]
                 :let [y (* x 2)]]
             y)))))

(deftest for-with-while-test
  (testing "for with :while short-circuit"
    (is (= '(1 2)
           (for [x      [1 2 3 4 5]
                 :while (< x 3)]
             x)))))

(run-all-tests)
