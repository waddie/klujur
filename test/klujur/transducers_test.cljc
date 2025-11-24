;; transducers_test.cljc - Tests for Klujur transducer operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.transducers-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Transduce
;; =============================================================================

(deftest transduce-test
  (testing "transduce with map"
    (is (= 12 (eval* "(transduce (map inc) + [1 2 3 4])"))))
  (testing "transduce with filter"
    (is (= 6 (eval* "(transduce (filter even?) + [1 2 3 4 5 6])"))))
  (testing "transduce with init"
    (is (= 20 (eval* "(transduce (map inc) + 10 [1 2 3 4])"))))
  (testing "transduce with composed xforms"
    (is (= 8
           (eval*
            "(transduce (comp (map inc) (filter even?)) + [1 2 3 4 5])")))))

;; =============================================================================
;; Reduced
;; =============================================================================

(deftest reduced-test
  (testing "reduced wraps value" (is (eval* "(reduced? (reduced 42))")))
  (testing "reduced? false for normal values"
    (is (false? (eval* "(reduced? 42)")))
    (is (false? (eval* "(reduced? nil)")))
    (is (false? (eval* "(reduced? [1 2 3])")))))

(deftest unreduced-test
  (testing "unreduced unwraps reduced"
    (is (= 42 (eval* "(unreduced (reduced 42))"))))
  (testing "unreduced returns non-reduced as-is"
    (is (= 42 (eval* "(unreduced 42)")))
    (is (= [1 2] (eval* "(unreduced [1 2])")))))

(deftest ensure-reduced-test
  (testing "ensure-reduced wraps non-reduced"
    (is (eval* "(reduced? (ensure-reduced 42))")))
  (testing "ensure-reduced preserves reduced"
    (is (eval* "(reduced? (ensure-reduced (reduced 42)))"))))

;; =============================================================================
;; Transducer Composition
;; =============================================================================

(deftest transducer-composition-test
  (testing "comp of transducers"
    (is (= [2 4]
           (eval* "(into [] (comp (map inc) (filter even?)) [1 2 3 4 5])"))))
  (testing "multiple transducers"
    (is (= [4 8]
           (eval* "(into [] (comp (filter even?) (map #(* 2 %))) [1 2 3 4])"))))
  (testing "comp is right-to-left for xforms"
    (is (= [3 5]
           (eval* "(into [] (comp (filter odd?) (map inc)) [1 2 3 4])")))))

;; =============================================================================
;; Transducer-returning Functions
;; =============================================================================

(deftest map-xf-test
  (testing "map as transducer"
    (is (= [2 3 4] (eval* "(into [] (map inc) [1 2 3])"))))
  (testing "map with multiple args as transducer"
    (is (= [5 7 9] (eval* "(into [] (map +) [[1 4] [2 5] [3 6]])")))))

(deftest filter-xf-test
  (testing "filter as transducer"
    (is (= [2 4] (eval* "(into [] (filter even?) [1 2 3 4 5])"))))
  (testing "filter with predicate"
    (is (= [1 2] (eval* "(into [] (filter #(< % 3)) [1 2 3 4])")))))

(deftest remove-xf-test
  (testing "remove as transducer"
    (is (= [1 3 5] (eval* "(into [] (remove even?) [1 2 3 4 5])")))))

(deftest take-xf-test
  (testing "take as transducer"
    (is (= [1 2 3] (eval* "(into [] (take 3) [1 2 3 4 5])"))))
  (testing "take more than available"
    (is (= [1 2] (eval* "(into [] (take 5) [1 2])")))))

(deftest drop-xf-test
  (testing "drop as transducer"
    (is (= [4 5] (eval* "(into [] (drop 3) [1 2 3 4 5])"))))
  (testing "drop more than available"
    (is (= [] (eval* "(into [] (drop 10) [1 2 3])")))))

(deftest take-while-xf-test
  (testing "take-while as transducer"
    (is (= [1 2] (eval* "(into [] (take-while #(< % 3)) [1 2 3 4 5])")))))

(deftest drop-while-xf-test
  (testing "drop-while as transducer"
    (is (= [3 4 5] (eval* "(into [] (drop-while #(< % 3)) [1 2 3 4 5])")))))

(deftest dedupe-xf-test
  (testing "dedupe as transducer"
    (is (= [1 2 3 2] (eval* "(into [] (dedupe) [1 1 2 2 2 3 2])")))))

(deftest partition-all-xf-test
  (testing "partition-all as transducer"
    (is (= [[1 2] [3 4] [5]]
           (eval* "(into [] (partition-all 2) [1 2 3 4 5])")))))

;; =============================================================================
;; Early Termination
;; =============================================================================

(deftest early-termination-test
  (testing "take terminates early"
    (is (= [1 2 3]
           (eval* "(transduce (take 3) conj [] [1 2 3 4 5 6 7 8 9 10])"))))
  (testing "reduced in reducing fn"
    (is
     (=
      6
      (eval*
       "(transduce identity
                              (fn [acc x] (if (> acc 5) (reduced acc) (+ acc x)))
                              0
                              [1 2 3 4 5])")))))

;; =============================================================================
;; cat Transducer
;; =============================================================================

(deftest cat-xf-test
  (testing "cat as transducer flattens one level"
    (is (= [1 2 3 4] (eval* "(into [] (cat) [[1 2] [3 4]])"))))
  (testing "cat with empty nested collections"
    (is (= [1 2] (eval* "(into [] (cat) [[1] [] [2] []])"))))
  (testing "cat with single element collections"
    (is (= [1 2 3] (eval* "(into [] (cat) [[1] [2] [3]])"))))
  (testing "cat with comp"
    (is (= [2 3 4 5] (eval* "(into [] (comp (cat) (map inc)) [[1 2] [3 4]])"))))
  (testing "cat in different order with comp"
    (is (= [[2 3] [4 5]]
           (eval* "(into [] (comp (map #(map inc %)) (cat)) [[1 2] [3 4]])")))))

(deftest mapcat-xf-test
  (testing "mapcat as transducer"
    (is (= [1 2 2 3 3 3] (eval* "(into [] (mapcat #(repeat % %)) [1 2 3])"))))
  (testing "mapcat with identity"
    (is (= [1 2 3 4] (eval* "(into [] (mapcat identity) [[1 2] [3 4]])")))))
