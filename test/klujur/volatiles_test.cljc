;; volatiles_test.cljc - Tests for Klujur volatile operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.volatiles-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Volatile Creation
;; =============================================================================

(deftest volatile-creation-test
  (testing "volatile! creates a volatile"
    (is (eval* "(volatile? (volatile! 0))")))
  (testing "volatile! with initial value"
    (is (= 42 (eval* "(deref (volatile! 42))"))))
  (testing "volatile! with various types"
    (is (= :foo (eval* "(deref (volatile! :foo))")))
    (is (= [1 2 3] (eval* "(deref (volatile! [1 2 3]))")))
    (is (= {:a 1} (eval* "(deref (volatile! {:a 1}))")))))

(deftest volatile-predicate-test
  (testing "volatile?"
    (is (true? (eval* "(volatile? (volatile! 0))")))
    (is (false? (eval* "(volatile? 42)")))
    (is (false? (eval* "(volatile? nil)")))
    (is (false? (eval* "(volatile? [])")))
    (is (false? (eval* "(volatile? (atom 0))")))))

;; =============================================================================
;; Dereferencing
;; =============================================================================

(deftest volatile-deref-test
  (testing "deref returns volatile value"
    (is (= 42 (eval* "(deref (volatile! 42))"))))
  (testing "@ reader macro works with volatiles"
    (is (= 100 (eval* "@(volatile! 100)"))))
  (testing "deref with nil value" (is (nil? (eval* "@(volatile! nil)")))))

;; =============================================================================
;; vreset! (set value)
;; =============================================================================

(deftest vreset-test
  (testing "vreset! replaces value"
    (is (= 100 (eval* "(let [v (volatile! 0)] (vreset! v 100) (deref v))"))))
  (testing "vreset! returns new value"
    (is (= 100 (eval* "(let [v (volatile! 0)] (vreset! v 100))"))))
  (testing "vreset! multiple times"
    (is
     (=
      3
      (eval*
       "(let [v (volatile! 0)]
                       (vreset! v 1)
                       (vreset! v 2)
                       (vreset! v 3)
                       @v)")))))

;; =============================================================================
;; vswap! (apply function to value)
;; =============================================================================

(deftest vswap-test
  (testing "vswap! applies function"
    (is (= 1 (eval* "(let [v (volatile! 0)] (vswap! v inc) @v)"))))
  (testing "vswap! with additional args"
    (is (= 10 (eval* "(let [v (volatile! 0)] (vswap! v + 10) @v)"))))
  (testing "vswap! with multiple args"
    (is (= 15 (eval* "(let [v (volatile! 0)] (vswap! v + 1 2 3 4 5) @v)"))))
  (testing "vswap! returns new value"
    (is (= 1 (eval* "(let [v (volatile! 0)] (vswap! v inc))"))))
  (testing "vswap! with collection"
    (is
     (=
      [1 2 3]
      (eval*
       "(let [v (volatile! [])]
                             (vswap! v conj 1)
                             (vswap! v conj 2)
                             (vswap! v conj 3)
                             @v)")))))

;; =============================================================================
;; Volatiles vs Atoms (volatiles are NOT thread-safe)
;; =============================================================================

(deftest volatile-characteristics-test
  (testing "volatiles are not atoms"
    (is (false? (eval* "(atom? (volatile! 0))"))))
  (testing "atoms are not volatiles"
    (is (false? (eval* "(volatile? (atom 0))"))))
  (testing "volatiles work with deref" (is (= 42 (eval* "@(volatile! 42)")))))

;; =============================================================================
;; Practical Use Cases (transducers, local state)
;; =============================================================================

(deftest volatile-use-cases-test
  (testing "volatile as counter in iteration"
    (is
     (=
      5
      (eval*
       "(let [counter (volatile! 0)]
                       (doseq [x [1 2 3 4 5]]
                         (vswap! counter inc))
                       @counter)"))))
  (testing "volatile as accumulator"
    (is
     (=
      [1 4 9 16]
      (eval*
       "(let [result (volatile! [])]
                                (doseq [x [1 2 3 4]]
                                  (vswap! result conj (* x x)))
                                @result)"))))
  (testing "volatile with conditional updates"
    (is
     (=
      [2 4]
      (eval*
       "(let [evens (volatile! [])]
                           (doseq [x [1 2 3 4 5]]
                             (when (even? x)
                               (vswap! evens conj x)))
                           @evens)")))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest volatile-error-cases-test
  (testing "vreset! requires a volatile"
    (is (thrown? Exception (eval* "(vreset! 42 100)"))))
  (testing "vswap! requires a volatile"
    (is (thrown? Exception (eval* "(vswap! 42 inc)"))))
  (testing "volatile! requires exactly one argument"
    (is (thrown? Exception (eval* "(volatile!)")))
    (is (thrown? Exception (eval* "(volatile! 1 2)"))))
  (testing "vreset! requires exactly two arguments"
    (is (thrown? Exception (eval* "(let [v (volatile! 0)] (vreset! v))")))
    (is (thrown? Exception (eval* "(let [v (volatile! 0)] (vreset! v 1 2))"))))
  (testing "vswap! requires at least two arguments"
    (is (thrown? Exception (eval* "(let [v (volatile! 0)] (vswap! v))")))))

;; =============================================================================
;; Volatiles in Collections
;; =============================================================================

(deftest volatiles-in-collections-test
  (testing "volatile stored in vector"
    (is
     (=
      42
      (eval*
       "(let [v (volatile! 42)
                             vec [v]]
                        @(first vec))"))))
  (testing "volatile stored in map"
    (is
     (=
      100
      (eval*
       "(let [v (volatile! 100)
                              m {:vol v}]
                         @(:vol m))"))))
  (testing "modifying volatile through collection"
    (is
     (=
      11
      (eval*
       "(let [v (volatile! 10)
                             vec [v]]
                        (vswap! (first vec) inc)
                        @v)")))))

;; =============================================================================
;; Complex Functions with vswap!
;; =============================================================================

(deftest vswap-complex-functions-test
  (testing "vswap! with anonymous function"
    (is
     (=
      25
      (eval*
       "(let [v (volatile! 5)]
                        (vswap! v (fn* [x] (* x x)))
                        @v)"))))
  (testing "vswap! with multi-arg function"
    (is
     (=
      {:a 1 :b 2}
      (eval*
       "(let [v (volatile! {})]
                                 (vswap! v assoc :a 1)
                                 (vswap! v assoc :b 2)
                                 @v)")))))

;; =============================================================================
;; Volatiles in Stateful Transducers
;; =============================================================================

(deftest volatile-in-transducer-test
  (testing "dedupe uses volatiles correctly for state"
    ;; dedupe uses volatiles internally to track previous value
    (is (= [1 2 3 2] (eval* "(into [] (dedupe) [1 1 2 2 3 3 2])")))
    (is (= [1 2 1] (eval* "(into [] (dedupe) [1 1 1 2 2 1 1])")))
    (is (= [] (eval* "(into [] (dedupe) [])"))))
  (testing "partition-by uses volatiles correctly for state"
    ;; partition-by uses volatiles to track current partition key
    (is (= [[1 1] [2 2] [1]]
           (eval* "(into [] (partition-by identity) [1 1 2 2 1])")))
    (is (= [[:a :a] [:b] [:a]]
           (eval* "(into [] (partition-by identity) [:a :a :b :a])")))
    (is (= [[1 3] [2 4]] (eval* "(into [] (partition-by even?) [1 3 2 4])")))))
