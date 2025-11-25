;; volatiles_test.cljc - Tests for Klujur volatile operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.volatiles-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Volatile Creation
;; =============================================================================

(deftest volatile-creation-test
  (testing "volatile! creates a volatile" (is (volatile? (volatile! 0))))
  (testing "volatile! with initial value" (is (= 42 (deref (volatile! 42)))))
  (testing "volatile! with various types"
    (is (= :foo (deref (volatile! :foo))))
    (is (= [1 2 3] (deref (volatile! [1 2 3]))))
    (is (= {:a 1} (deref (volatile! {:a 1}))))))

(deftest volatile-predicate-test
  (testing "volatile?"
    (is (true? (volatile? (volatile! 0))))
    (is (false? (volatile? 42)))
    (is (false? (volatile? nil)))
    (is (false? (volatile? [])))
    (is (false? (volatile? (atom 0))))))

;; =============================================================================
;; Dereferencing
;; =============================================================================

(deftest volatile-deref-test
  (testing "deref returns volatile value" (is (= 42 (deref (volatile! 42)))))
  (testing "@ reader macro works with volatiles" (is (= 100 @(volatile! 100))))
  (testing "deref with nil value" (is (nil? @(volatile! nil)))))

;; =============================================================================
;; vreset! (set value)
;; =============================================================================

(deftest vreset-test
  (testing "vreset! replaces value"
    (is (= 100
           (let [v (volatile! 0)]
             (vreset! v 100)
             (deref v)))))
  (testing "vreset! returns new value"
    (is (= 100
           (let [v (volatile! 0)]
             (vreset! v 100)))))
  (testing "vreset! multiple times"
    (is (= 3
           (let [v (volatile! 0)]
             (vreset! v 1)
             (vreset! v 2)
             (vreset! v 3)
             @v)))))

;; =============================================================================
;; vswap! (apply function to value)
;; =============================================================================

(deftest vswap-test
  (testing "vswap! applies function"
    (is (= 1
           (let [v (volatile! 0)]
             (vswap! v inc)
             @v))))
  (testing "vswap! with additional args"
    (is (= 10
           (let [v (volatile! 0)]
             (vswap! v + 10)
             @v))))
  (testing "vswap! with multiple args"
    (is (= 15
           (let [v (volatile! 0)]
             (vswap! v + 1 2 3 4 5)
             @v))))
  (testing "vswap! returns new value"
    (is (= 1
           (let [v (volatile! 0)]
             (vswap! v inc)))))
  (testing "vswap! with collection"
    (is (= [1 2 3]
           (let [v (volatile! [])]
             (vswap! v conj 1)
             (vswap! v conj 2)
             (vswap! v conj 3)
             @v)))))

;; =============================================================================
;; Volatiles vs Atoms (volatiles are NOT thread-safe)
;; =============================================================================

(deftest volatile-characteristics-test
  (testing "volatiles are not atoms" (is (false? (atom? (volatile! 0)))))
  (testing "atoms are not volatiles" (is (false? (volatile? (atom 0)))))
  (testing "volatiles work with deref" (is (= 42 @(volatile! 42)))))

;; =============================================================================
;; Practical Use Cases (transducers, local state)
;; =============================================================================

(deftest volatile-use-cases-test
  (testing "volatile as counter in iteration"
    (is (= 5
           (let [counter (volatile! 0)]
             (doseq [x [1 2 3 4 5]]
               (vswap! counter inc))
             @counter))))
  (testing "volatile as accumulator"
    (is (= [1 4 9 16]
           (let [result (volatile! [])]
             (doseq [x [1 2 3 4]]
               (vswap! result conj (* x x)))
             @result))))
  (testing "volatile with conditional updates"
    (is (= [2 4]
           (let [evens (volatile! [])]
             (doseq [x [1 2 3 4 5]]
               (when (even? x) (vswap! evens conj x)))
             @evens)))))

;; =============================================================================
;; Error Cases
;; =============================================================================

(deftest volatile-error-cases-test
  (testing "vreset! requires a volatile"
    (is (thrown? Exception (vreset! 42 100))))
  (testing "vswap! requires a volatile"
    (is (thrown? Exception (vswap! 42 inc))))
  (testing "volatile! requires exactly one argument"
    (is (thrown? Exception (volatile!)))
    (is (thrown? Exception (volatile! 1 2))))
  (testing "vreset! requires exactly two arguments"
    (is (thrown? Exception
                 (let [v (volatile! 0)]
                   (vreset! v))))
    (is (thrown? Exception
                 (let [v (volatile! 0)]
                   (vreset! v 1 2)))))
  (testing "vswap! requires at least two arguments"
    (is (thrown? Exception
                 (let [v (volatile! 0)]
                   (vswap! v))))))

;; =============================================================================
;; Volatiles in Collections
;; =============================================================================

(deftest volatiles-in-collections-test
  (testing "volatile stored in vector"
    (is (= 42
           (let [v   (volatile! 42)
                 vec [v]]
             @(first vec)))))
  (testing "volatile stored in map"
    (is (= 100
           (let [v (volatile! 100)
                 m {:vol v}]
             @(:vol m)))))
  (testing "modifying volatile through collection"
    (is (= 11
           (let [v   (volatile! 10)
                 vec [v]]
             (vswap! (first vec) inc)
             @v)))))

;; =============================================================================
;; Complex Functions with vswap!
;; =============================================================================

(deftest vswap-complex-functions-test
  (testing "vswap! with anonymous function"
    (is (= 25
           (let [v (volatile! 5)]
             (vswap! v (fn* [x] (* x x)))
             @v))))
  (testing "vswap! with multi-arg function"
    (is (= {:a 1 :b 2}
           (let [v (volatile! {})]
             (vswap! v assoc :a 1)
             (vswap! v assoc :b 2)
             @v)))))

;; =============================================================================
;; Volatiles in Stateful Transducers
;; =============================================================================

(deftest volatile-in-transducer-test
  (testing "dedupe uses volatiles correctly for state"
    ;; dedupe uses volatiles internally to track previous value
    (is (= [1 2 3 2] (into [] (dedupe) [1 1 2 2 3 3 2])))
    (is (= [1 2 1] (into [] (dedupe) [1 1 1 2 2 1 1])))
    (is (= [] (into [] (dedupe) []))))
  (testing "partition-by uses volatiles correctly for state"
    ;; partition-by uses volatiles to track current partition key
    (is (= [[1 1] [2 2] [1]] (into [] (partition-by identity) [1 1 2 2 1])))
    (is (= [[:a :a] [:b] [:a]] (into [] (partition-by identity) [:a :a :b :a])))
    (is (= [[1 3] [2 4]] (into [] (partition-by even?) [1 3 2 4])))))

(run-all-tests)
