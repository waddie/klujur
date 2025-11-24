;; datetime_test.cljc - Tests for Klujur date/time operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.datetime-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; System Time (milliseconds since Unix epoch)
;; =============================================================================

(deftest system-time-test
  (testing "system-time returns positive integer"
    (let [result (eval* "(system-time)")]
      (is (integer? result))
      (is (pos? result))))
  (testing "system-time returns value near current time"
    ;; Should be sometime after 2020 (timestamp > 1577836800000)
    (let [result (eval* "(system-time)")]
      (is (> result 1577836800000))))
  (testing "system-time progresses"
    (let [t1 (eval* "(system-time)")
          _ (Thread/sleep 10) ; Wait a bit
          t2 (eval* "(system-time)")]
      (is (>= t2 t1)))))

;; =============================================================================
;; Now Millis (alias for system-time)
;; =============================================================================

(deftest now-millis-test
  (testing "now-millis returns positive integer"
    (let [result (eval* "(now-millis)")]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-millis matches system-time"
    ;; These should be very close in value (within a few milliseconds)
    (let [t1 (eval* "(system-time)")
          t2 (eval* "(now-millis)")]
      (is (< (Math/abs (- t2 t1)) 100)))))

;; =============================================================================
;; Now Nanoseconds
;; =============================================================================

(deftest now-nanos-test
  (testing "now-nanos returns positive integer"
    (let [result (eval* "(now-nanos)")]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-nanos is larger than now-millis"
    ;; Nanoseconds should be ~1,000,000 times larger than milliseconds
    (let [millis (eval* "(now-millis)")
          nanos  (eval* "(now-nanos)")]
      (is (> nanos (* millis 1000000)))))
  (testing "now-nanos progresses"
    (let [t1 (eval* "(now-nanos)")
          _ (Thread/sleep 1)
          t2 (eval* "(now-nanos)")]
      (is (> t2 t1)))))

;; =============================================================================
;; Now Microseconds
;; =============================================================================

(deftest now-micros-test
  (testing "now-micros returns positive integer"
    (let [result (eval* "(now-micros)")]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-micros is between millis and nanos"
    ;; Microseconds should be ~1,000 times larger than milliseconds
    ;; and ~1,000 times smaller than nanoseconds
    (let [millis (eval* "(now-millis)")
          micros (eval* "(now-micros)")]
      (is (> micros (* millis 1000)))))
  (testing "now-micros progresses"
    (let [t1 (eval* "(now-micros)")
          _ (Thread/sleep 1)
          t2 (eval* "(now-micros)")]
      (is (> t2 t1)))))

;; =============================================================================
;; Now Seconds
;; =============================================================================

(deftest now-secs-test
  (testing "now-secs returns positive integer"
    (let [result (eval* "(now-secs)")]
      (is (integer? result))
      (is (pos? result))))
  (testing "now-secs is smaller than now-millis"
    ;; Seconds should be ~1,000 times smaller than milliseconds
    (let [millis (eval* "(now-millis)")
          secs   (eval* "(now-secs)")]
      (is (< (* secs 1000) (+ millis 1000))))) ; Allow 1 second tolerance
  (testing "now-secs returns value after 2020"
    ;; Should be sometime after 2020 (timestamp > 1577836800)
    (let [result (eval* "(now-secs)")]
      (is (> result 1577836800)))))

;; =============================================================================
;; Relative Timing
;; =============================================================================

(deftest time-unit-relationships-test
  (testing "time units are properly scaled"
    ;; Get all time values around the same moment
    (let [millis (eval* "(now-millis)")
          micros (eval* "(now-micros)")
          nanos  (eval* "(now-nanos)")
          secs   (eval* "(now-secs)")]
      ;; Verify rough ordering (allowing for small timing differences)
      (is (> nanos micros))
      (is (> micros millis))
      (is (< secs millis)))))

;; =============================================================================
;; Arity Errors
;; =============================================================================

(deftest datetime-arity-errors-test
  (testing "system-time requires no arguments"
    (is (thrown? Exception (eval* "(system-time 123)"))))
  (testing "now-millis requires no arguments"
    (is (thrown? Exception (eval* "(now-millis 123)"))))
  (testing "now-nanos requires no arguments"
    (is (thrown? Exception (eval* "(now-nanos 123)"))))
  (testing "now-micros requires no arguments"
    (is (thrown? Exception (eval* "(now-micros 123)"))))
  (testing "now-secs requires no arguments"
    (is (thrown? Exception (eval* "(now-secs 123)")))))

;; =============================================================================
;; Practical Use Cases
;; =============================================================================

(deftest timing-operations-test
  (testing "can measure elapsed time with now-millis"
    (let [start    (eval* "(def start (now-millis))")
          _ (Thread/sleep 50) ; Do some work
          duration (eval* "(- (now-millis) start)")]
      (is (>= duration 40)) ; Should be at least 40ms
      (is (< duration 200)))) ; But not too long
  (testing "can use now-secs for timestamp"
    (let [timestamp (eval* "(now-secs)")]
      ;; Should be a reasonable Unix timestamp
      (is (> timestamp 1000000000)) ; After Sep 2001
      (is (< timestamp 3000000000))))) ; Before Jan 2065

;; =============================================================================
;; Time Value Types
;; =============================================================================

(deftest time-value-types-test
  (testing "all time functions return integers"
    (is (integer? (eval* "(system-time)")))
    (is (integer? (eval* "(now-millis)")))
    (is (integer? (eval* "(now-nanos)")))
    (is (integer? (eval* "(now-micros)")))
    (is (integer? (eval* "(now-secs)")))))
