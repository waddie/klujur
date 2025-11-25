;; lazy_seqs_test.cljc - Tests for Klujur lazy sequence operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.lazy-seqs-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Lazy-seq Special Form
;; =============================================================================

(deftest lazy-seq-test
  (testing "lazy-seq creates lazy sequence" (is (seq? (lazy-seq (cons 1 nil)))))
  (testing "lazy-seq defers evaluation"
    (is (= [1]
           (let [effect (atom false)]
             (def ls (lazy-seq (reset! effect true) [1]))
             (if (deref effect) :eager :lazy)
             (doall ls)
             (if (deref effect) [1] :not-realized)))))
  (testing "lazy-seq with cons"
    (is (= '(1 2 3)
           (let [f (fn f [n] (lazy-seq (when (< n 4) (cons n (f (inc n))))))]
             (doall (f 1)))))))

;; =============================================================================
;; Delay and Force
;; =============================================================================

(deftest delay-test
  (testing "delay creates delay" (is (delay? (delay 42))))
  (testing "delay defers evaluation"
    (is (= :lazy
           (let [effect (atom :lazy)]
             (def d (delay (reset! effect :eager)))
             (deref effect)))))
  (testing "force evaluates delay" (is (= 42 (force (delay 42)))))
  (testing "force returns non-delay as-is" (is (= 42 (force 42)))))

(deftest delay-memoization-test
  (testing "delay memoizes result"
    (is (= 1
           (let [counter (atom 0)
                 d       (delay (swap! counter inc))]
             (force d)
             (force d)
             (force d)
             (deref counter))))))

;; =============================================================================
;; Realized?
;; =============================================================================

(deftest realized-test
  (testing "realized? on unrealized delay" (is (false? (realized? (delay 42)))))
  (testing "realized? on realized delay"
    (is (true? (let [d (delay 42)]
                 (force d)
                 (realized? d)))))
  (testing "realized? on lazy-seq" (is (false? (realized? (lazy-seq [1 2 3])))))
  (testing "realized? on forced lazy-seq"
    (is (true? (let [ls (lazy-seq [1 2 3])]
                 (first ls)
                 (realized? ls))))))

;; =============================================================================
;; Doall and Dorun
;; =============================================================================

(deftest doall-test
  (testing "doall forces entire sequence"
    (is (= '(1 2 3) (doall (map identity '(1 2 3))))))
  (testing "doall returns the seq" (is (= '(2 3 4) (doall (map inc '(1 2 3))))))
  (testing "doall with n" (is (= '(1 2 3 4 5) (take 5 (doall 5 (range)))))))

(deftest dorun-test
  (testing "dorun returns nil" (is (nil? (dorun (map identity '(1 2 3))))))
  (testing "dorun with n" (is (nil? (dorun 5 (range))))))

;; =============================================================================
;; Memoize
;; =============================================================================

(deftest memoize-test
  (testing "memoize caches results"
    (is (= 1
           (let [counter (atom 0)
                 f       (fn [x] (swap! counter inc) (* x 2))
                 mf      (memoize f)]
             (mf 5)
             (mf 5)
             (mf 5)
             (deref counter)))))
  (testing "memoize different args"
    (is (= 3
           (let [counter (atom 0)
                 f       (fn [x] (swap! counter inc) (* x 2))
                 mf      (memoize f)]
             (mf 1)
             (mf 2)
             (mf 3)
             (deref counter))))))

;; =============================================================================
;; Infinite Sequences
;; =============================================================================

(deftest infinite-range-test
  (testing "0-arity range is infinite" (is (= '(0 1 2 3 4) (take 5 (range)))))
  (testing "range with step" (is (= '(0 2 4 6 8) (take 5 (range 0 100 2))))))

(deftest infinite-repeat-test
  (testing "1-arity repeat is infinite"
    (is (= '(:x :x :x :x :x) (take 5 (repeat :x)))))
  (testing "2-arity repeat is finite"
    (is (= '(:y :y :y) (doall (repeat 3 :y))))))

(deftest iterate-test
  (testing "iterate generates infinite sequence"
    (is (= '(1 2 4 8 16) (take 5 (iterate #(* 2 %) 1)))))
  (testing "iterate with inc" (is (= '(0 1 2 3 4) (take 5 (iterate inc 0))))))

(deftest cycle-test
  (testing "cycle repeats sequence"
    (is (= '(1 2 3 1 2 3 1) (take 7 (cycle [1 2 3])))))
  (testing "cycle with small seq"
    (is (= '(:a :b :a :b :a) (take 5 (cycle [:a :b]))))))

(deftest repeatedly-test
  (testing "repeatedly with 0-arity fn"
    (is (= 5 (count (take 5 (repeatedly (fn [] 42)))))))
  (testing "repeatedly with n" (is (= 3 (count (repeatedly 3 (fn [] :x)))))))

(run-all-tests)
