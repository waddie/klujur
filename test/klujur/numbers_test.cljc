;; numbers_test.cljc - Tests for Klujur numeric operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.numbers-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; Helper for approximate equality
(defn approx=
  ([a b] (approx= a b 0.00001))
  ([a b epsilon] (< (abs (- a b)) epsilon)))

;; =============================================================================
;; Basic Arithmetic
;; =============================================================================

(deftest addition-test
  (testing "+"
    (is (= 0 (+))) ; identity
    (is (= 1 (+ 1)))
    (is (= 3 (+ 1 2)))
    (is (= 10 (+ 1 2 3 4)))
    (is (= 5.5 (+ 2.5 3.0)))))

(deftest subtraction-test
  (testing "-"
    (is (= -1 (- 1))) ; negation
    (is (= 1 (- 3 2)))
    (is (= -4 (- 1 2 3)))
    (is (= 2.5 (- 5.0 2.5)))))

(deftest multiplication-test
  (testing "*"
    (is (= 1 (*))) ; identity
    (is (= 5 (* 5)))
    (is (= 6 (* 2 3)))
    (is (= 24 (* 1 2 3 4)))
    (is (= 7.5 (* 2.5 3.0)))))

(deftest division-test
  (testing "/"
    (is (= 1/2 (/ 2))) ; reciprocal
    (is (= 2 (/ 6 3)))
    (is (= 2 (/ 12 3 2)))
    (is (= 2.5 (/ 5.0 2.0)))))

(deftest division-by-zero-test
  (testing "division by zero"
    (is (thrown? Exception (/ 1 0)))
    ;; Float division by zero may produce Infinity
    (is (infinite? (/ 1.0 0.0)))))

;; =============================================================================
;; Integer Division and Modulo
;; =============================================================================

(deftest quot-test
  (testing "quot (integer division)"
    (is (= 3 (quot 10 3)))
    (is (= -3 (quot -10 3)))
    (is (= -3 (quot 10 -3)))
    (is (= 3 (quot -10 -3)))))

(deftest rem-test
  (testing "rem (remainder)"
    (is (= 1 (rem 10 3)))
    (is (= -1 (rem -10 3))) ; sign follows dividend
    (is (= 1 (rem 10 -3)))
    (is (= -1 (rem -10 -3)))))

(deftest mod-test
  (testing "mod (modulus)"
    (is (= 1 (mod 10 3)))
    (is (= 2 (mod -10 3))) ; sign follows divisor
    (is (= -2 (mod 10 -3)))
    (is (= -1 (mod -10 -3)))))

;; =============================================================================
;; Comparisons
;; =============================================================================

(deftest equality-test
  (testing "="
    (is (true? (= 1 1)))
    (is (true? (= 1 1 1 1)))
    (is (false? (= 1 2)))
    (is (false? (= 1 1 2)))
    (is (true? (= 1.0 1.0)))
    ;; Integer and float comparison
    (is (true? (= 1 1.0))) ; numeric equality
    (is (true? (=)))))          ; vacuous truth

(deftest not-equal-test
  (testing "not="
    (is (true? (not= 1 2)))
    (is (false? (not= 1 1)))
    (is (true? (not= 1 2 3)))
    (is (false? (not= 1 1 1)))))

(deftest less-than-test
  (testing "<"
    (is (true? (< 1 2)))
    (is (false? (< 2 1)))
    (is (false? (< 1 1)))
    (is (true? (< 1 2 3 4)))
    (is (false? (< 1 2 2 3))) ; not strictly increasing
    (is (true? (<)))))          ; vacuous truth

(deftest less-than-or-equal-test
  (testing "<="
    (is (true? (<= 1 2)))
    (is (true? (<= 1 1)))
    (is (false? (<= 2 1)))
    (is (true? (<= 1 2 2 3)))
    (is (false? (<= 1 3 2)))))

(deftest greater-than-test
  (testing ">"
    (is (true? (> 2 1)))
    (is (false? (> 1 2)))
    (is (false? (> 1 1)))
    (is (true? (> 4 3 2 1)))
    (is (false? (> 4 3 3 1)))))

(deftest greater-than-or-equal-test
  (testing ">="
    (is (true? (>= 2 1)))
    (is (true? (>= 1 1)))
    (is (false? (>= 1 2)))
    (is (true? (>= 4 3 3 1)))))

(deftest compare-test
  (testing "compare"
    (is (neg? (compare 1 2)))
    (is (zero? (compare 1 1)))
    (is (pos? (compare 2 1)))))

;; =============================================================================
;; Numeric Predicates
;; =============================================================================

(deftest number-predicate-test
  (testing "number?"
    (is (true? (number? 1)))
    (is (true? (number? 1.5)))
    (is (true? (number? 1/2)))
    (is (false? (number? "1")))
    (is (false? (number? nil)))))

(deftest integer-predicate-test
  (testing "integer?"
    (is (true? (integer? 1)))
    (is (true? (integer? -5)))
    (is (false? (integer? 1.0))) ; float, not integer
    (is (false? (integer? 1/2)))))

(deftest float-predicate-test
  (testing "float?"
    (is (true? (float? 1.0)))
    (is (true? (float? 1.5)))
    (is (false? (float? 1)))
    (is (false? (float? 1/2)))))

(deftest ratio-predicate-test
  (testing "ratio?"
    (is (true? (ratio? 1/2)))
    (is (true? (ratio? 3/4)))
    (is (false? (ratio? 1)))
    (is (false? (ratio? 1.0)))
    (is (false? (ratio? 2/2)))))  ; reduces to 1

(deftest zero-predicate-test
  (testing "zero?"
    (is (true? (zero? 0)))
    (is (true? (zero? 0.0)))
    (is (false? (zero? 1)))
    (is (false? (zero? -1)))))

(deftest pos-predicate-test
  (testing "pos?"
    (is (true? (pos? 1)))
    (is (true? (pos? 0.1)))
    (is (false? (pos? 0)))
    (is (false? (pos? -1)))))

(deftest neg-predicate-test
  (testing "neg?"
    (is (true? (neg? -1)))
    (is (true? (neg? -0.1)))
    (is (false? (neg? 0)))
    (is (false? (neg? 1)))))

(deftest even-predicate-test
  (testing "even?"
    (is (true? (even? 0)))
    (is (true? (even? 2)))
    (is (true? (even? -4)))
    (is (false? (even? 1)))
    (is (false? (even? -3)))))

(deftest odd-predicate-test
  (testing "odd?"
    (is (true? (odd? 1)))
    (is (true? (odd? -3)))
    (is (false? (odd? 0)))
    (is (false? (odd? 2)))))

(deftest pos-int-predicate-test
  (testing "pos-int?"
    (is (true? (pos-int? 1)))
    (is (false? (pos-int? 0)))
    (is (false? (pos-int? -1)))
    (is (false? (pos-int? 1.0)))))

(deftest neg-int-predicate-test
  (testing "neg-int?"
    (is (true? (neg-int? -1)))
    (is (false? (neg-int? 0)))
    (is (false? (neg-int? 1)))
    (is (false? (neg-int? -1.0)))))

(deftest nat-int-predicate-test
  (testing "nat-int? (natural integer, >= 0)"
    (is (true? (nat-int? 0)))
    (is (true? (nat-int? 1)))
    (is (false? (nat-int? -1)))
    (is (false? (nat-int? 1.0)))))

(deftest NaN-predicate-test
  (testing "NaN?"
    (is (true? (NaN? ##NaN)))
    (is (false? (NaN? 1.0)))
    (is (false? (NaN? ##Inf)))))

(deftest infinite-predicate-test
  (testing "infinite?"
    (is (true? (infinite? ##Inf)))
    (is (true? (infinite? ##-Inf)))
    (is (false? (infinite? 1.0)))
    (is (false? (infinite? ##NaN)))))

;; =============================================================================
;; Math Functions
;; =============================================================================

(deftest inc-dec-test
  (testing "inc" (is (= 2 (inc 1))) (is (= 0 (inc -1))) (is (= 1.5 (inc 0.5))))
  (testing "dec"
    (is (= 0 (dec 1)))
    (is (= -2 (dec -1)))
    (is (= -0.5 (dec 0.5)))))

(deftest max-min-test
  (testing "max"
    (is (= 5 (max 1 5 3)))
    (is (= 1 (max 1)))
    (is (= 5.0 (max 1.0 5.0 3.0))))
  (testing "min"
    (is (= 1 (min 1 5 3)))
    (is (= 1 (min 1)))
    (is (= 1.0 (min 1.0 5.0 3.0)))))

(deftest abs-test
  (testing "abs"
    (is (= 5 (abs 5)))
    (is (= 5 (abs -5)))
    (is (= 0 (abs 0)))
    (is (= 5.5 (abs -5.5)))))

(deftest Math-functions-test
  (testing "sqrt" (is (= 2.0 (sqrt 4))) (is (= 3.0 (sqrt 9))))
  (testing "pow" (is (= 8.0 (pow 2 3))) (is (= 1.0 (pow 5 0))))
  (testing "floor and ceil" (is (= 3.0 (floor 3.7))) (is (= 4.0 (ceil 3.2))))
  (testing "round" (is (= 4 (round 3.5))) (is (= 3 (round 3.4)))))

(deftest trig-functions-test
  (testing "trigonometric functions"
    (is (approx= 0.0 (sin 0) 0.0001))
    (is (approx= 1.0 (cos 0) 0.0001))
    (is (approx= 0.0 (tan 0) 0.0001))))

(deftest exp-log-test
  (testing "exp" (is (= 1.0 (exp 0))) (is (approx= 2.718281828 (exp 1) 0.0001)))
  (testing "log" (is (= 0.0 (log 1)))))

;; =============================================================================
;; Bit Operations
;; =============================================================================

(deftest bit-and-test
  (testing "bit-and"
    (is (= 0 (bit-and 1 2)))
    (is (= 1 (bit-and 1 3)))
    (is (= 2 (bit-and 2 3)))))

(deftest bit-or-test
  (testing "bit-or"
    (is (= 3 (bit-or 1 2)))
    (is (= 3 (bit-or 1 3)))
    (is (= 7 (bit-or 3 4)))))

(deftest bit-xor-test
  (testing "bit-xor"
    (is (= 3 (bit-xor 1 2)))
    (is (= 2 (bit-xor 1 3)))
    (is (= 0 (bit-xor 5 5)))))

(deftest bit-not-test
  (testing "bit-not"
    (is (= -1 (bit-not 0)))
    (is (= -2 (bit-not 1)))
    (is (= 0 (bit-not -1)))))

(deftest bit-shift-test
  (testing "bit-shift-left"
    (is (= 2 (bit-shift-left 1 1)))
    (is (= 8 (bit-shift-left 1 3)))
    (is (= 16 (bit-shift-left 2 3))))
  (testing "bit-shift-right"
    (is (= 1 (bit-shift-right 2 1)))
    (is (= 1 (bit-shift-right 8 3)))
    (is (= 4 (bit-shift-right 16 2)))))

(deftest bit-test-test
  (testing "bit-test"
    (is (true? (bit-test 5 0)))  ; bit 0 of 101 is 1
    (is (false? (bit-test 5 1))) ; bit 1 of 101 is 0
    (is (true? (bit-test 5 2)))))  ; bit 2 of 101 is 1

(deftest bit-set-clear-flip-test
  (testing "bit-set" (is (= 5 (bit-set 4 0))) (is (= 7 (bit-set 5 1))))
  (testing "bit-clear" (is (= 4 (bit-clear 5 0))) (is (= 1 (bit-clear 5 2))))
  (testing "bit-flip" (is (= 4 (bit-flip 5 0))) (is (= 7 (bit-flip 5 1)))))

;; =============================================================================
;; Random Numbers
;; =============================================================================

(deftest rand-test
  (testing "rand"
    (let [r (rand)]
      (is (number? r))
      (is (>= r 0.0))
      (is (< r 1.0))))
  (testing "rand with max"
    (let [r (rand 10)]
      (is (number? r))
      (is (>= r 0.0))
      (is (< r 10.0)))))

(deftest rand-int-test
  (testing "rand-int"
    (let [r (rand-int 10)]
      (is (integer? r))
      (is (>= r 0))
      (is (< r 10)))))

(deftest rand-nth-test
  (testing "rand-nth"
    (let [r (rand-nth [1 2 3 4 5])]
      (is (contains? #{1 2 3 4 5} r)))))

(deftest shuffle-test
  (testing "shuffle"
    (let [coll (shuffle [1 2 3 4 5])]
      (is (= (set coll) #{1 2 3 4 5}))
      (is (= (count coll) 5)))))

;; =============================================================================
;; Integer Overflow Edge Cases
;; =============================================================================

(deftest overflow-boundaries-test
  (testing "operations at i64::MAX boundary"
    ;; i64::MAX = 9223372036854775807
    (is (= 9223372036854775807 9223372036854775807))
    (is (= 9223372036854775807 (+ 9223372036854775807 0)))
    (is (= 9223372036854775806 (- 9223372036854775807 1))))
  (testing "operations at i64::MIN boundary"
    ;; i64::MIN = -9223372036854775808
    (is (= -9223372036854775808 -9223372036854775808))
    (is (= -9223372036854775807 (+ -9223372036854775808 1)))
    (is (= -9223372036854775808 (- -9223372036854775807 1)))))

(deftest overflow-errors-test
  (testing "addition overflow"
    (is (thrown? Exception (+ 9223372036854775807 1)))
    (is (thrown? Exception (+ -9223372036854775808 -1))))
  (testing "subtraction overflow"
    (is (thrown? Exception (- 9223372036854775807 -1)))
    (is (thrown? Exception (- -9223372036854775808 1))))
  (testing "multiplication overflow"
    (is (thrown? Exception (* 9223372036854775807 2)))
    (is (thrown? Exception (* 3037000500 3037000500))))
  (testing "inc/dec overflow"
    (is (thrown? Exception (inc 9223372036854775807)))
    (is (thrown? Exception (dec -9223372036854775808))))
  (testing "abs overflow"
    ;; abs(MIN) overflows because |MIN| > MAX
    (is (thrown? Exception (abs -9223372036854775808)))
    ;; abs(MAX) is fine
    (is (= 9223372036854775807 (abs 9223372036854775807)))
    ;; abs(MIN + 1) = MAX
    (is (= 9223372036854775807 (abs -9223372036854775807)))))

(deftest overflow-negation-test
  (testing "unary negation at boundaries"
    ;; -MAX is valid
    (is (= -9223372036854775807 (- 9223372036854775807)))
    ;; -MIN overflows
    (is (thrown? Exception (- -9223372036854775808)))))

(deftest overflow-multi-arg-test
  (testing "multi-argument overflow"
    ;; Multiple large additions that overflow
    (is (thrown?
         Exception
         (+ 4000000000000000000 4000000000000000000 4000000000000000000)))
    ;; Chained multiplication that overflows
    (is (thrown? Exception (* 10000000000 10000000000 10000000000)))))

(deftest overflow-no-error-with-floats-test
  (testing "floats go to infinity, no overflow error"
    ;; Float arithmetic doesn't throw overflow errors
    (let [result (+ 1.0e308 1.0e308)]
      (is (infinite? result)))
    ;; Mixed int/float uses float arithmetic
    (is (number? (+ 9223372036854775807 1.0)))))

;; =============================================================================
;; BigInt Auto-Promoting Operators
;; =============================================================================

(deftest bigint-auto-promoting-operators-test
  (testing "+' auto-promotes to BigInt on overflow"
    (is (= 9223372036854775808 (+' 9223372036854775807 1)))
    (is (= -9223372036854775809 (+' -9223372036854775808 -1))))
  (testing "-' auto-promotes to BigInt on overflow"
    (is (= 9223372036854775808 (-' 9223372036854775807 -1)))
    (is (= -9223372036854775809 (-' -9223372036854775808 1))))
  (testing "*' auto-promotes to BigInt on overflow"
    (is (= 18446744073709551614 (*' 9223372036854775807 2)))
    (is (= 9223372036854775809 (*' 3037000500 3037000500)))))

(deftest bigint-inc-dec-promoting-test
  (testing "inc' auto-promotes to BigInt"
    (is (= 9223372036854775808 (inc' 9223372036854775807))))
  (testing "dec' auto-promotes to BigInt"
    (is (= -9223372036854775809 (dec' -9223372036854775808)))))

(deftest bigint-literal-auto-promotion-test
  (testing "literals beyond i64 auto-promote to BigInt"
    (is (true? (bigint? 9223372036854775808)))
    (is (false? (bigint? 9223372036854775807))))
  (testing "integer? returns true for both Int and BigInt"
    (is (true? (integer? 9223372036854775807)))
    (is (true? (integer? 9223372036854775808)))))

(run-all-tests)
