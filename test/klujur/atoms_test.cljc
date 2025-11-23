;; atoms_test.cljc - Tests for Klujur atom operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.atoms-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Atom Creation
;; =============================================================================

(deftest atom-creation-test
  (testing "atom creates an atom" (is (eval* "(atom? (atom 0))")))
  (testing "atom with initial value" (is (= 42 (eval* "(deref (atom 42))"))))
  (testing "atom with various types"
    (is (= :foo (eval* "(deref (atom :foo))")))
    (is (= [1 2 3] (eval* "(deref (atom [1 2 3]))")))
    (is (= {:a 1} (eval* "(deref (atom {:a 1}))")))))

(deftest atom-predicate-test
  (testing "atom?"
    (is (true? (eval* "(atom? (atom 0))")))
    (is (false? (eval* "(atom? 42)")))
    (is (false? (eval* "(atom? nil)")))
    (is (false? (eval* "(atom? []))")))))

;; =============================================================================
;; Reset and Swap
;; =============================================================================

(deftest reset-test
  (testing "reset! replaces value"
    (is (= 100 (eval* "(let [a (atom 0)] (reset! a 100) (deref a))"))))
  (testing "reset! returns new value"
    (is (= 100 (eval* "(let [a (atom 0)] (reset! a 100))")))))

(deftest reset-vals-test
  (testing "reset-vals! returns [old new]"
    (is (= [0 100] (eval* "(let [a (atom 0)] (reset-vals! a 100))")))
    (is (= [42 :new] (eval* "(let [a (atom 42)] (reset-vals! a :new))")))))

(deftest swap-test
  (testing "swap! applies function"
    (is (= 1 (eval* "(let [a (atom 0)] (swap! a inc) (deref a))")))
    (is (= 10 (eval* "(let [a (atom 5)] (swap! a * 2) (deref a))"))))
  (testing "swap! with multiple args"
    (is (= 15 (eval* "(let [a (atom 0)] (swap! a + 1 2 3 4 5) (deref a))"))))
  (testing "swap! returns new value"
    (is (= 1 (eval* "(let [a (atom 0)] (swap! a inc))")))))

(deftest swap-vals-test
  (testing "swap-vals! returns [old new]"
    (is (= [0 1] (eval* "(let [a (atom 0)] (swap-vals! a inc))")))
    (is (= [5 10] (eval* "(let [a (atom 5)] (swap-vals! a * 2))")))))

(deftest compare-and-set-test
  (testing "compare-and-set! success"
    (is (true? (eval* "(let [a (atom 0)] (compare-and-set! a 0 1))")))
    (is (= 1 (eval* "(let [a (atom 0)] (compare-and-set! a 0 1) (deref a))"))))
  (testing "compare-and-set! failure"
    (is (false? (eval* "(let [a (atom 0)] (compare-and-set! a 999 1))")))
    (is (= 0
           (eval* "(let [a (atom 0)] (compare-and-set! a 999 1) (deref a))")))))

;; =============================================================================
;; Watches
;; =============================================================================

(deftest add-watch-test
  (testing "add-watch returns atom"
    (is (eval* "(atom? (add-watch (atom 0) :test (fn [k r o n])))")))
  (testing "watch is called on change"
    (is
     (=
      [:test 0 1]
      (eval*
       "(let [result (atom nil)
                         a (atom 0)]
                     (add-watch a :test (fn [k r o n] (reset! result [k o n])))
                     (reset! a 1)
                     (deref result))")))))

(deftest remove-watch-test
  (testing "remove-watch returns atom"
    (is (eval* "(atom? (remove-watch (atom 0) :test))")))
  (testing "removed watch not called"
    (is
     (nil?
      (eval*
       "(let [result (atom nil)
                            a (atom 0)]
                        (add-watch a :test (fn [k r o n] (reset! result :called)))
                        (remove-watch a :test)
                        (reset! a 1)
                        (deref result))")))))

;; =============================================================================
;; Validators
;; =============================================================================

(deftest validator-test
  (testing "set-validator! accepts valid value"
    (is
     (=
      5
      (eval*
       "(let [a (atom 0)]
                       (set-validator! a pos?)
                       (reset! a 5)
                       (deref a))"))))
  (testing "get-validator returns validator"
    (is
     (eval*
      "(fn? (let [a (atom 0)]
                        (set-validator! a pos?)
                        (get-validator a)))")))
  (testing "nil validator clears"
    (is
     (nil?
      (eval*
       "(let [a (atom 0)]
                         (set-validator! a pos?)
                         (set-validator! a nil)
                         (get-validator a))")))))
