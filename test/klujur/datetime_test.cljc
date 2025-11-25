;; datetime_test.cljc - Tests for Klujur date/time operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.datetime-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]
            [klujur.time :refer
             [system-time now-millis now-nanos now-micros now-secs]]))

;; =============================================================================
;; System Time (milliseconds since Unix epoch)
;; =============================================================================

(deftest system-time-test
  (testing "system-time returns positive integer"
    (let [result (system-time)]
      (is (integer? result))
      (is (pos? result))))
  (testing "system-time returns value near current time"
    ;; Should be sometime after 2020 (timestamp > 1577836800000)
    (let [result (system-time)]
      (is (> result 1577836800000)))))

;; =============================================================================
;; Now Millis (alias for system-time)
;; =============================================================================

(deftest now-millis-test
  (testing "now-millis returns positive integer"
    (let [result (now-millis)]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-millis close to system-time"
    ;; These should be very close in value (within a few milliseconds)
    (let [t1 (system-time)
          t2 (now-millis)]
      (is (< (abs (- t2 t1)) 100)))))

;; =============================================================================
;; Now Nanoseconds
;; =============================================================================

(deftest now-nanos-test
  (testing "now-nanos returns positive integer"
    (let [result (now-nanos)]
      (is (integer? result))
      (is (pos? result)))))

;; =============================================================================
;; Now Microseconds
;; =============================================================================

(deftest now-micros-test
  (testing "now-micros returns positive integer"
    (let [result (now-micros)]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-micros is larger than millis"
    ;; Microseconds should be ~1,000 times larger than milliseconds
    (let [millis (now-millis)
          micros (now-micros)]
      (is (> micros (* millis 1000))))))

;; =============================================================================
;; Now Seconds
;; =============================================================================

(deftest now-secs-test
  (testing "now-secs returns positive integer"
    (let [result (now-secs)]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-secs is smaller than now-millis"
    ;; Seconds should be ~1,000 times smaller than milliseconds
    (let [millis (now-millis)
          secs   (now-secs)]
      (is (< (* secs 1000) (+ millis 1000))))) ; Allow 1 second tolerance
  (testing "now-secs returns value after 2020"
    ;; Should be sometime after 2020 (timestamp > 1577836800)
    (let [result (now-secs)]
      (is (> result 1577836800)))))

;; =============================================================================
;; Relative Timing
;; =============================================================================

(deftest time-unit-relationships-test
  (testing "time units are properly scaled"
    ;; Get all time values around the same moment
    (let [millis (now-millis)
          micros (now-micros)
          nanos  (now-nanos)
          secs   (now-secs)]
      ;; Verify rough ordering (allowing for small timing differences)
      (is (> nanos micros))
      (is (> micros millis))
      (is (< secs millis)))))

;; =============================================================================
;; Arity Errors
;; =============================================================================

(deftest datetime-arity-errors-test
  (testing "system-time requires no arguments"
    (is (thrown? Exception (system-time 123))))
  (testing "now-millis requires no arguments"
    (is (thrown? Exception (now-millis 123))))
  (testing "now-nanos requires no arguments"
    (is (thrown? Exception (now-nanos 123))))
  (testing "now-micros requires no arguments"
    (is (thrown? Exception (now-micros 123))))
  (testing "now-secs requires no arguments"
    (is (thrown? Exception (now-secs 123)))))

;; =============================================================================
;; Practical Use Cases
;; =============================================================================

(deftest timing-operations-test
  (testing "can use now-secs for timestamp"
    (let [timestamp (now-secs)]
      ;; Should be a reasonable Unix timestamp
      (is (> timestamp 1000000000)) ; After Sep 2001
      (is (< timestamp 3000000000))))) ; Before Jan 2065

;; =============================================================================
;; Time Value Types
;; =============================================================================

(deftest time-value-types-test
  (testing "all time functions return integers"
    (is (integer? (system-time)))
    (is (integer? (now-millis)))
    (is (integer? (now-nanos)))
    (is (integer? (now-micros)))
    (is (integer? (now-secs)))))

(run-all-tests)
