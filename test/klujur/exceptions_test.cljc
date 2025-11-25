;; exceptions_test.cljc - Tests for Klujur exception handling
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.exceptions-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Try/Catch/Finally
;; =============================================================================

(deftest try-basic-test
  (testing "try without exception"
    (is (= 42 (try 42)))
    (is (= 3 (try (+ 1 2))))))

(deftest catch-test
  (testing "catch catches exception"
    (is (= :caught (try (throw "error") (catch Exception e :caught)))))
  (testing "catch binds exception"
    (is (= "error" (try (throw "error") (catch Exception e e)))))
  (testing "catch with ex-info"
    (is (= {:reason :test}
           (try (throw (ex-info "msg" {:reason :test}))
                (catch Exception e (ex-data e)))))))

(deftest finally-test
  (testing "finally executes after try"
    (is (= [1 :finally]
           (let [log (atom [])]
             (try (swap! log conj 1) (finally (swap! log conj :finally)))
             (deref log)))))
  (testing "finally executes after catch"
    (is (= [:caught :finally]
           (let [log (atom [])]
             (try (throw "error")
                  (catch Exception e (swap! log conj :caught))
                  (finally (swap! log conj :finally)))
             (deref log)))))
  (testing "finally return value not used"
    (is (= 42 (try 42 (finally :ignored))))))

(deftest nested-try-test
  (testing "nested try/catch"
    (is (= :inner
           (try (try (throw "inner") (catch Exception e :inner))
                (catch Exception e :outer)))))
  (testing "exception propagates to outer"
    (is (= :outer (try (try (throw "error")) (catch Exception e :outer))))))

;; =============================================================================
;; Throw
;; =============================================================================

(deftest throw-test
  (testing "throw string"
    (is (= "error" (try (throw "error") (catch Exception e e)))))
  (testing "throw with ex-info"
    (is (= "message"
           (try (throw (ex-info "message" {:a 1}))
                (catch Exception e (ex-message e)))))))

;; =============================================================================
;; Ex-info Functions
;; =============================================================================

(deftest ex-info-test
  (testing "ex-info creates exception" (is (map? (ex-info "msg" {:a 1}))))
  (testing "ex-info with cause" (is (map? (ex-info "msg" {:a 1} "cause")))))

(deftest ex-data-test
  (testing "ex-data returns map"
    (is (= {:reason :test} (ex-data (ex-info "msg" {:reason :test})))))
  (testing "ex-data on non-ex-info" (is (nil? (ex-data "plain string")))))

(deftest ex-message-test
  (testing "ex-message returns message"
    (is (= "test message" (ex-message (ex-info "test message" {})))))
  (testing "ex-message on string" (is (= "hello" (ex-message "hello")))))

;; =============================================================================
;; Multiple Catch Clauses
;; =============================================================================

(deftest multiple-catch-test
  (testing "first matching catch"
    (is (= :exception
           (try (throw (ex-info "error" {:type :test}))
                (catch Exception e :exception))))))

(run-all-tests)
