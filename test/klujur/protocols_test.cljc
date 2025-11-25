;; protocols_test.cljc - Tests for Klujur protocol operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.protocols-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Protocol Definition
;; =============================================================================

(deftest defprotocol-test
  (testing "defprotocol creates protocol"
    (is (do (defprotocol IFoo
              (foo [x]))
            (protocol? IFoo))))
  (testing "protocol method is callable"
    (is (do (defprotocol IBar
              (bar [x]))
            (extend-type String
             IBar
               (bar [x] :string))
            (= :string (bar "test"))))))

;; =============================================================================
;; Extend-type
;; =============================================================================

(deftest extend-type-test
  (testing "extend-type with single method"
    (is (= :nil-result
           (do (defprotocol ITest
                 (process [x]))
               (extend-type nil
                ITest
                  (process [x] :nil-result))
               (process nil)))))
  (testing "extend-type with multiple methods"
    (is (= [1 2]
           (do (defprotocol IMulti
                 (method-a [x])
                 (method-b [x]))
               (extend-type Vector
                IMulti
                  (method-a [x] (first x))
                  (method-b [x] (second x)))
               [(method-a [1 2 3]) (method-b [1 2 3])])))))

(deftest extend-type-various-types-test
  (testing "extend to nil"
    (is (= :nil-value
           (do (defprotocol INil
                 (nil-test [x]))
               (extend-type nil
                INil
                  (nil-test [x] :nil-value))
               (nil-test nil)))))
  (testing "extend to Vector"
    (is (= 3
           (do (defprotocol ILen
                 (len [x]))
               (extend-type Vector
                ILen
                  (len [x] (count x)))
               (len [1 2 3])))))
  (testing "extend to Map"
    (is (= [:a :b]
           (do (defprotocol IKeys
                 (get-keys [x]))
               (extend-type Map
                IKeys
                  (get-keys [x] (keys x)))
               (vec (get-keys {:a 1 :b 2})))))))

;; =============================================================================
;; Satisfies and Extends
;; =============================================================================

(deftest satisfies-test
  (testing "satisfies? returns true when extended"
    (is (true? (do (defprotocol ISat
                     (sat-fn [x]))
                   (extend-type String
                    ISat
                      (sat-fn [x] x))
                   (satisfies? ISat "test")))))
  (testing "satisfies? returns false when not extended"
    (is (false? (do (defprotocol INotSat
                      (not-sat-fn [x]))
                    (satisfies? INotSat 42))))))

(deftest extends-test
  (testing "extends? returns true for extended type"
    (is (true? (do (defprotocol IExt
                     (ext-fn [x]))
                   (extend-type Vector
                    IExt
                      (ext-fn [x] x))
                   (extends? IExt Vector)))))
  (testing "extends? returns false for non-extended type"
    (is (false? (do (defprotocol INotExt
                      (not-ext-fn [x]))
                    (extends? INotExt Map))))))

;; =============================================================================
;; Protocol Dispatch
;; =============================================================================

(deftest protocol-dispatch-test
  (testing "dispatch to correct implementation"
    (is (= [:vector :list :nil]
           (do (defprotocol IDispatch
                 (dispatch-test [x]))
               (extend-type Vector
                IDispatch
                  (dispatch-test [x] :vector))
               (extend-type List
                IDispatch
                  (dispatch-test [x] :list))
               (extend-type nil
                IDispatch
                  (dispatch-test [x] :nil))
               [(dispatch-test [1 2]) (dispatch-test '(1 2))
                (dispatch-test nil)]))))
  (testing "method with additional args"
    (is (= 15
           (do (defprotocol IWithArgs
                 (with-args [x y z]))
               (extend-type Int
                IWithArgs
                  (with-args [x y z] (+ x y z)))
               (with-args 5 4 6))))))

(run-all-tests)
