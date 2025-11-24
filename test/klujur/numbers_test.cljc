;; numbers_test.cljc - Tests for Klujur numeric operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.numbers-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval* approx=]]))

;; =============================================================================
;; Basic Arithmetic
;; =============================================================================

(deftest addition-test
  (testing "+"
    (is (= 0 (eval* "(+)"))) ; identity
    (is (= 1 (eval* "(+ 1)")))
    (is (= 3 (eval* "(+ 1 2)")))
    (is (= 10 (eval* "(+ 1 2 3 4)")))
    (is (= 5.5 (eval* "(+ 2.5 3.0)")))))

(deftest subtraction-test
  (testing "-"
    (is (= -1 (eval* "(- 1)"))) ; negation
    (is (= 1 (eval* "(- 3 2)")))
    (is (= -4 (eval* "(- 1 2 3)")))
    (is (= 2.5 (eval* "(- 5.0 2.5)")))))

(deftest multiplication-test
  (testing "*"
    (is (= 1 (eval* "(*)"))) ; identity
    (is (= 5 (eval* "(* 5)")))
    (is (= 6 (eval* "(* 2 3)")))
    (is (= 24 (eval* "(* 1 2 3 4)")))
    (is (= 7.5 (eval* "(* 2.5 3.0)")))))

(deftest division-test
  (testing "/"
    (is (= 1/2 (eval* "(/ 2)"))) ; reciprocal
    (is (= 2 (eval* "(/ 6 3)")))
    (is (= 2 (eval* "(/ 12 3 2)")))
    (is (= 2.5 (eval* "(/ 5.0 2.0)")))))

(deftest division-by-zero-test
  (testing "division by zero"
    (is (thrown? #?(:clj ArithmeticException
                    :cljs js/Error)
                 (eval* "(/ 1 0)")))
    ;; Float division by zero may produce Infinity
    (is (Double/isInfinite (eval* "(/ 1.0 0.0)")))))

;; =============================================================================
;; Integer Division and Modulo
;; =============================================================================

(deftest quot-test
  (testing "quot (integer division)"
    (is (= 3 (eval* "(quot 10 3)")))
    (is (= -3 (eval* "(quot -10 3)")))
    (is (= -3 (eval* "(quot 10 -3)")))
    (is (= 3 (eval* "(quot -10 -3)")))))

(deftest rem-test
  (testing "rem (remainder)"
    (is (= 1 (eval* "(rem 10 3)")))
    (is (= -1 (eval* "(rem -10 3)"))) ; sign follows dividend
    (is (= 1 (eval* "(rem 10 -3)")))
    (is (= -1 (eval* "(rem -10 -3)")))))

(deftest mod-test
  (testing "mod (modulus)"
    (is (= 1 (eval* "(mod 10 3)")))
    (is (= 2 (eval* "(mod -10 3)"))) ; sign follows divisor
    (is (= -2 (eval* "(mod 10 -3)")))
    (is (= -1 (eval* "(mod -10 -3)")))))

;; =============================================================================
;; Comparisons
;; =============================================================================

(deftest equality-test
  (testing "="
    (is (true? (eval* "(= 1 1)")))
    (is (true? (eval* "(= 1 1 1 1)")))
    (is (false? (eval* "(= 1 2)")))
    (is (false? (eval* "(= 1 1 2)")))
    (is (true? (eval* "(= 1.0 1.0)")))
    ;; Integer and float comparison
    (is (true? (eval* "(= 1 1.0)"))) ; numeric equality
    (is (true? (eval* "(=)")))))          ; vacuous truth

(deftest not-equal-test
  (testing "not="
    (is (true? (eval* "(not= 1 2)")))
    (is (false? (eval* "(not= 1 1)")))
    (is (true? (eval* "(not= 1 2 3)")))
    (is (false? (eval* "(not= 1 1 1)")))))

(deftest less-than-test
  (testing "<"
    (is (true? (eval* "(< 1 2)")))
    (is (false? (eval* "(< 2 1)")))
    (is (false? (eval* "(< 1 1)")))
    (is (true? (eval* "(< 1 2 3 4)")))
    (is (false? (eval* "(< 1 2 2 3)"))) ; not strictly increasing
    (is (true? (eval* "(<)")))))          ; vacuous truth

(deftest less-than-or-equal-test
  (testing "<="
    (is (true? (eval* "(<= 1 2)")))
    (is (true? (eval* "(<= 1 1)")))
    (is (false? (eval* "(<= 2 1)")))
    (is (true? (eval* "(<= 1 2 2 3)")))
    (is (false? (eval* "(<= 1 3 2)")))))

(deftest greater-than-test
  (testing ">"
    (is (true? (eval* "(> 2 1)")))
    (is (false? (eval* "(> 1 2)")))
    (is (false? (eval* "(> 1 1)")))
    (is (true? (eval* "(> 4 3 2 1)")))
    (is (false? (eval* "(> 4 3 3 1)")))))

(deftest greater-than-or-equal-test
  (testing ">="
    (is (true? (eval* "(>= 2 1)")))
    (is (true? (eval* "(>= 1 1)")))
    (is (false? (eval* "(>= 1 2)")))
    (is (true? (eval* "(>= 4 3 3 1)")))))

(deftest compare-test
  (testing "compare"
    (is (neg? (eval* "(compare 1 2)")))
    (is (zero? (eval* "(compare 1 1)")))
    (is (pos? (eval* "(compare 2 1)")))))

;; =============================================================================
;; Numeric Predicates
;; =============================================================================

(deftest number-predicate-test
  (testing "number?"
    (is (true? (eval* "(number? 1)")))
    (is (true? (eval* "(number? 1.5)")))
    (is (true? (eval* "(number? 1/2)")))
    (is (false? (eval* "(number? \"1\")")))
    (is (false? (eval* "(number? nil)")))))

(deftest integer-predicate-test
  (testing "integer?"
    (is (true? (eval* "(integer? 1)")))
    (is (true? (eval* "(integer? -5)")))
    (is (false? (eval* "(integer? 1.0)"))) ; float, not integer
    (is (false? (eval* "(integer? 1/2)")))))

(deftest float-predicate-test
  (testing "float?"
    (is (true? (eval* "(float? 1.0)")))
    (is (true? (eval* "(float? 1.5)")))
    (is (false? (eval* "(float? 1)")))
    (is (false? (eval* "(float? 1/2)")))))

(deftest ratio-predicate-test
  (testing "ratio?"
    (is (true? (eval* "(ratio? 1/2)")))
    (is (true? (eval* "(ratio? 3/4)")))
    (is (false? (eval* "(ratio? 1)")))
    (is (false? (eval* "(ratio? 1.0)")))
    (is (false? (eval* "(ratio? 2/2)")))))  ; reduces to 1

(deftest zero-predicate-test
  (testing "zero?"
    (is (true? (eval* "(zero? 0)")))
    (is (true? (eval* "(zero? 0.0)")))
    (is (false? (eval* "(zero? 1)")))
    (is (false? (eval* "(zero? -1)")))))

(deftest pos-predicate-test
  (testing "pos?"
    (is (true? (eval* "(pos? 1)")))
    (is (true? (eval* "(pos? 0.1)")))
    (is (false? (eval* "(pos? 0)")))
    (is (false? (eval* "(pos? -1)")))))

(deftest neg-predicate-test
  (testing "neg?"
    (is (true? (eval* "(neg? -1)")))
    (is (true? (eval* "(neg? -0.1)")))
    (is (false? (eval* "(neg? 0)")))
    (is (false? (eval* "(neg? 1)")))))

(deftest even-predicate-test
  (testing "even?"
    (is (true? (eval* "(even? 0)")))
    (is (true? (eval* "(even? 2)")))
    (is (true? (eval* "(even? -4)")))
    (is (false? (eval* "(even? 1)")))
    (is (false? (eval* "(even? -3)")))))

(deftest odd-predicate-test
  (testing "odd?"
    (is (true? (eval* "(odd? 1)")))
    (is (true? (eval* "(odd? -3)")))
    (is (false? (eval* "(odd? 0)")))
    (is (false? (eval* "(odd? 2)")))))

(deftest pos-int-predicate-test
  (testing "pos-int?"
    (is (true? (eval* "(pos-int? 1)")))
    (is (false? (eval* "(pos-int? 0)")))
    (is (false? (eval* "(pos-int? -1)")))
    (is (false? (eval* "(pos-int? 1.0)")))))

(deftest neg-int-predicate-test
  (testing "neg-int?"
    (is (true? (eval* "(neg-int? -1)")))
    (is (false? (eval* "(neg-int? 0)")))
    (is (false? (eval* "(neg-int? 1)")))
    (is (false? (eval* "(neg-int? -1.0)")))))

(deftest nat-int-predicate-test
  (testing "nat-int? (natural integer, >= 0)"
    (is (true? (eval* "(nat-int? 0)")))
    (is (true? (eval* "(nat-int? 1)")))
    (is (false? (eval* "(nat-int? -1)")))
    (is (false? (eval* "(nat-int? 1.0)")))))

(deftest NaN-predicate-test
  (testing "NaN?"
    (is (true? (eval* "(NaN? ##NaN)")))
    (is (false? (eval* "(NaN? 1.0)")))
    (is (false? (eval* "(NaN? ##Inf)")))))

(deftest infinite-predicate-test
  (testing "infinite?"
    (is (true? (eval* "(infinite? ##Inf)")))
    (is (true? (eval* "(infinite? ##-Inf)")))
    (is (false? (eval* "(infinite? 1.0)")))
    (is (false? (eval* "(infinite? ##NaN)")))))

;; =============================================================================
;; Math Functions
;; =============================================================================

(deftest inc-dec-test
  (testing "inc"
    (is (= 2 (eval* "(inc 1)")))
    (is (= 0 (eval* "(inc -1)")))
    (is (= 1.5 (eval* "(inc 0.5)"))))
  (testing "dec"
    (is (= 0 (eval* "(dec 1)")))
    (is (= -2 (eval* "(dec -1)")))
    (is (= -0.5 (eval* "(dec 0.5)")))))

(deftest max-min-test
  (testing "max"
    (is (= 5 (eval* "(max 1 5 3)")))
    (is (= 1 (eval* "(max 1)")))
    (is (= 5.0 (eval* "(max 1.0 5.0 3.0)"))))
  (testing "min"
    (is (= 1 (eval* "(min 1 5 3)")))
    (is (= 1 (eval* "(min 1)")))
    (is (= 1.0 (eval* "(min 1.0 5.0 3.0)")))))

(deftest abs-test
  (testing "abs"
    (is (= 5 (eval* "(abs 5)")))
    (is (= 5 (eval* "(abs -5)")))
    (is (= 0 (eval* "(abs 0)")))
    (is (= 5.5 (eval* "(abs -5.5)")))))

(deftest Math-functions-test
  (testing "Math/sqrt"
    (is (= 2.0 (eval* "(Math/sqrt 4)")))
    (is (= 3.0 (eval* "(Math/sqrt 9)"))))
  (testing "Math/pow"
    (is (= 8.0 (eval* "(Math/pow 2 3)")))
    (is (= 1.0 (eval* "(Math/pow 5 0)"))))
  (testing "Math/floor and Math/ceil"
    (is (= 3.0 (eval* "(Math/floor 3.7)")))
    (is (= 4.0 (eval* "(Math/ceil 3.2)"))))
  (testing "Math/round"
    (is (= 4 (eval* "(Math/round 3.5)")))
    (is (= 3 (eval* "(Math/round 3.4)")))))

(deftest trig-functions-test
  (testing "trigonometric functions"
    (is (approx= 0.0 (eval* "(Math/sin 0)") 0.0001))
    (is (approx= 1.0 (eval* "(Math/cos 0)") 0.0001))
    (is (approx= 0.0 (eval* "(Math/tan 0)") 0.0001))))

(deftest exp-log-test
  (testing "Math/exp"
    (is (= 1.0 (eval* "(Math/exp 0)")))
    (is (approx= 2.718281828 (eval* "(Math/exp 1)") 0.0001)))
  (testing "Math/log"
    (is (= 0.0 (eval* "(Math/log 1)")))
    (is (approx= 1.0 (eval* "(Math/log Math/E)") 0.0001))))

;; =============================================================================
;; Bit Operations
;; =============================================================================

(deftest bit-and-test
  (testing "bit-and"
    (is (= 0 (eval* "(bit-and 1 2)")))
    (is (= 1 (eval* "(bit-and 1 3)")))
    (is (= 2 (eval* "(bit-and 2 3)")))))

(deftest bit-or-test
  (testing "bit-or"
    (is (= 3 (eval* "(bit-or 1 2)")))
    (is (= 3 (eval* "(bit-or 1 3)")))
    (is (= 7 (eval* "(bit-or 3 4)")))))

(deftest bit-xor-test
  (testing "bit-xor"
    (is (= 3 (eval* "(bit-xor 1 2)")))
    (is (= 2 (eval* "(bit-xor 1 3)")))
    (is (= 0 (eval* "(bit-xor 5 5)")))))

(deftest bit-not-test
  (testing "bit-not"
    (is (= -1 (eval* "(bit-not 0)")))
    (is (= -2 (eval* "(bit-not 1)")))
    (is (= 0 (eval* "(bit-not -1)")))))

(deftest bit-shift-test
  (testing "bit-shift-left"
    (is (= 2 (eval* "(bit-shift-left 1 1)")))
    (is (= 8 (eval* "(bit-shift-left 1 3)")))
    (is (= 16 (eval* "(bit-shift-left 2 3)"))))
  (testing "bit-shift-right"
    (is (= 1 (eval* "(bit-shift-right 2 1)")))
    (is (= 1 (eval* "(bit-shift-right 8 3)")))
    (is (= 4 (eval* "(bit-shift-right 16 2)")))))

(deftest bit-test-test
  (testing "bit-test"
    (is (true? (eval* "(bit-test 5 0)")))  ; bit 0 of 101 is 1
    (is (false? (eval* "(bit-test 5 1)"))) ; bit 1 of 101 is 0
    (is (true? (eval* "(bit-test 5 2)")))))  ; bit 2 of 101 is 1

(deftest bit-set-clear-flip-test
  (testing "bit-set"
    (is (= 5 (eval* "(bit-set 4 0)")))
    (is (= 7 (eval* "(bit-set 5 1)"))))
  (testing "bit-clear"
    (is (= 4 (eval* "(bit-clear 5 0)")))
    (is (= 1 (eval* "(bit-clear 5 2)"))))
  (testing "bit-flip"
    (is (= 4 (eval* "(bit-flip 5 0)")))
    (is (= 7 (eval* "(bit-flip 5 1)")))))

;; =============================================================================
;; Random Numbers
;; =============================================================================

(deftest rand-test
  (testing "rand"
    (let [r (eval* "(rand)")]
      (is (number? r))
      (is (>= r 0.0))
      (is (< r 1.0))))
  (testing "rand with max"
    (let [r (eval* "(rand 10)")]
      (is (number? r))
      (is (>= r 0.0))
      (is (< r 10.0)))))

(deftest rand-int-test
  (testing "rand-int"
    (let [r (eval* "(rand-int 10)")]
      (is (integer? r))
      (is (>= r 0))
      (is (< r 10)))))

(deftest rand-nth-test
  (testing "rand-nth"
    (let [r (eval* "(rand-nth [1 2 3 4 5])")]
      (is (contains? #{1 2 3 4 5} r)))))

(deftest shuffle-test
  (testing "shuffle"
    (let [coll (eval* "(shuffle [1 2 3 4 5])")]
      (is (= (set coll) #{1 2 3 4 5}))
      (is (= (count coll) 5)))))

;; =============================================================================
;; Integer Overflow Edge Cases
;; =============================================================================

(deftest overflow-boundaries-test
  (testing "operations at i64::MAX boundary"
    ;; i64::MAX = 9223372036854775807
    (is (= 9223372036854775807 (eval* "9223372036854775807")))
    (is (= 9223372036854775807 (eval* "(+ 9223372036854775807 0)")))
    (is (= 9223372036854775806 (eval* "(- 9223372036854775807 1)"))))
  (testing "operations at i64::MIN boundary"
    ;; i64::MIN = -9223372036854775808
    (is (= -9223372036854775808 (eval* "-9223372036854775808")))
    (is (= -9223372036854775807 (eval* "(+ -9223372036854775808 1)")))
    (is (= -9223372036854775808 (eval* "(- -9223372036854775807 1)")))))

(deftest overflow-errors-test
  (testing "addition overflow"
    (is (thrown? Exception (eval* "(+ 9223372036854775807 1)")))
    (is (thrown? Exception (eval* "(+ -9223372036854775808 -1)"))))
  (testing "subtraction overflow"
    (is (thrown? Exception (eval* "(- 9223372036854775807 -1)")))
    (is (thrown? Exception (eval* "(- -9223372036854775808 1)"))))
  (testing "multiplication overflow"
    (is (thrown? Exception (eval* "(* 9223372036854775807 2)")))
    (is (thrown? Exception (eval* "(* 3037000500 3037000500)"))))
  (testing "inc/dec overflow"
    (is (thrown? Exception (eval* "(inc 9223372036854775807)")))
    (is (thrown? Exception (eval* "(dec -9223372036854775808)"))))
  (testing "abs overflow"
    ;; abs(MIN) overflows because |MIN| > MAX
    (is (thrown? Exception (eval* "(abs -9223372036854775808)")))
    ;; abs(MAX) is fine
    (is (= 9223372036854775807 (eval* "(abs 9223372036854775807)")))
    ;; abs(MIN + 1) = MAX
    (is (= 9223372036854775807 (eval* "(abs -9223372036854775807)")))))

(deftest overflow-negation-test
  (testing "unary negation at boundaries"
    ;; -MAX is valid
    (is (= -9223372036854775807 (eval* "(- 9223372036854775807)")))
    ;; -MIN overflows
    (is (thrown? Exception (eval* "(- -9223372036854775808)")))))

(deftest overflow-multi-arg-test
  (testing "multi-argument overflow"
    ;; Multiple large additions that overflow
    (is (thrown?
         Exception
         (eval*
          "(+ 4000000000000000000 4000000000000000000 4000000000000000000)")))
    ;; Chained multiplication that overflows
    (is (thrown? Exception (eval* "(* 10000000000 10000000000 10000000000)")))))

(deftest overflow-no-error-with-floats-test
  (testing "floats go to infinity, no overflow error"
    ;; Float arithmetic doesn't throw overflow errors
    (let [result (eval* "(+ 1.0e308 1.0e308)")]
      (is (infinite? result)))
    ;; Mixed int/float uses float arithmetic
    (is (number? (eval* "(+ 9223372036854775807 1.0)")))))

;; =============================================================================
;; BigInt Auto-Promoting Operators
;; =============================================================================

(deftest bigint-auto-promoting-operators-test
  (testing "+' auto-promotes to BigInt on overflow"
    (is (= 9223372036854775808N (eval* "(+' 9223372036854775807 1)")))
    (is (= -9223372036854775809N (eval* "(+' -9223372036854775808 -1)"))))
  (testing "-' auto-promotes to BigInt on overflow"
    (is (= 9223372036854775808N (eval* "(-' 9223372036854775807 -1)")))
    (is (= -9223372036854775809N (eval* "(-' -9223372036854775808 1)"))))
  (testing "*' auto-promotes to BigInt on overflow"
    (is (= 18446744073709551614N (eval* "(*' 9223372036854775807 2)")))
    (is (= 9223372036854775809N (eval* "(*' 3037000500 3037000500)")))))

(deftest bigint-inc-dec-promoting-test
  (testing "inc' auto-promotes to BigInt"
    (is (= 9223372036854775808N (eval* "(inc' 9223372036854775807)"))))
  (testing "dec' auto-promotes to BigInt"
    (is (= -9223372036854775809N (eval* "(dec' -9223372036854775808)")))))

(deftest bigint-literal-auto-promotion-test
  (testing "literals beyond i64 auto-promote to BigInt"
    (is (true? (eval* "(bigint? 9223372036854775808)")))
    (is (false? (eval* "(bigint? 9223372036854775807)"))))
  (testing "integer? returns true for both Int and BigInt"
    (is (true? (eval* "(integer? 9223372036854775807)")))
    (is (true? (eval* "(integer? 9223372036854775808)")))))
