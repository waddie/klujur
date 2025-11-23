;; lazy_seqs_test.cljc - Tests for Klujur lazy sequence operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.lazy-seqs-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Lazy-seq Special Form
;; =============================================================================

(deftest lazy-seq-test
  (testing "lazy-seq creates lazy sequence"
    (is (eval* "(seq? (lazy-seq (cons 1 nil)))")))
  (testing "lazy-seq defers evaluation"
    (is
     (=
      [1]
      (eval*
       "(let [effect (atom false)]
                     (def ls (lazy-seq (reset! effect true) [1]))
                     (if (deref effect) :eager :lazy)
                     (doall ls)
                     (if (deref effect) [1] :not-realized))"))))
  (testing "lazy-seq with cons"
    (is
     (=
      '(1 2 3)
      (eval*
       "(let [f (fn f [n] (lazy-seq (when (< n 4) (cons n (f (inc n))))))]
                     (doall (f 1)))")))))

;; =============================================================================
;; Delay and Force
;; =============================================================================

(deftest delay-test
  (testing "delay creates delay" (is (eval* "(delay? (delay 42))")))
  (testing "delay defers evaluation"
    (is
     (=
      :lazy
      (eval*
       "(let [effect (atom :lazy)]
                     (def d (delay (reset! effect :eager)))
                     (deref effect))"))))
  (testing "force evaluates delay" (is (= 42 (eval* "(force (delay 42))"))))
  (testing "force returns non-delay as-is" (is (= 42 (eval* "(force 42)")))))

(deftest delay-memoization-test
  (testing "delay memoizes result"
    (is
     (=
      1
      (eval*
       "(let [counter (atom 0)
                         d (delay (swap! counter inc))]
                     (force d)
                     (force d)
                     (force d)
                     (deref counter))")))))

;; =============================================================================
;; Realized?
;; =============================================================================

(deftest realized-test
  (testing "realized? on unrealized delay"
    (is (false? (eval* "(realized? (delay 42))"))))
  (testing "realized? on realized delay"
    (is (true? (eval* "(let [d (delay 42)] (force d) (realized? d))"))))
  (testing "realized? on lazy-seq"
    (is (false? (eval* "(realized? (lazy-seq [1 2 3]))"))))
  (testing "realized? on forced lazy-seq"
    (is (true? (eval*
                "(let [ls (lazy-seq [1 2 3])] (first ls) (realized? ls))")))))

;; =============================================================================
;; Doall and Dorun
;; =============================================================================

(deftest doall-test
  (testing "doall forces entire sequence"
    (is (= '(1 2 3) (eval* "(doall (map identity '(1 2 3)))"))))
  (testing "doall returns the seq"
    (is (= '(2 3 4) (eval* "(doall (map inc '(1 2 3)))"))))
  (testing "doall with n"
    (is (= '(1 2 3 4 5) (eval* "(take 5 (doall 5 (range)))")))))

(deftest dorun-test
  (testing "dorun returns nil"
    (is (nil? (eval* "(dorun (map identity '(1 2 3)))"))))
  (testing "dorun with n" (is (nil? (eval* "(dorun 5 (range))")))))

;; =============================================================================
;; Memoize
;; =============================================================================

(deftest memoize-test
  (testing "memoize caches results"
    (is
     (=
      1
      (eval*
       "(let [counter (atom 0)
                         f (fn [x] (swap! counter inc) (* x 2))
                         mf (memoize f)]
                     (mf 5)
                     (mf 5)
                     (mf 5)
                     (deref counter))"))))
  (testing "memoize different args"
    (is
     (=
      3
      (eval*
       "(let [counter (atom 0)
                         f (fn [x] (swap! counter inc) (* x 2))
                         mf (memoize f)]
                     (mf 1)
                     (mf 2)
                     (mf 3)
                     (deref counter))")))))

;; =============================================================================
;; Infinite Sequences
;; =============================================================================

(deftest infinite-range-test
  (testing "0-arity range is infinite"
    (is (= '(0 1 2 3 4) (eval* "(take 5 (range))"))))
  (testing "range with step"
    (is (= '(0 2 4 6 8) (eval* "(take 5 (range 0 100 2))")))))

(deftest infinite-repeat-test
  (testing "1-arity repeat is infinite"
    (is (= '(:x :x :x :x :x) (eval* "(take 5 (repeat :x))"))))
  (testing "2-arity repeat is finite"
    (is (= '(:y :y :y) (eval* "(doall (repeat 3 :y))")))))

(deftest iterate-test
  (testing "iterate generates infinite sequence"
    (is (= '(1 2 4 8 16) (eval* "(take 5 (iterate #(* 2 %) 1))"))))
  (testing "iterate with inc"
    (is (= '(0 1 2 3 4) (eval* "(take 5 (iterate inc 0))")))))

(deftest cycle-test
  (testing "cycle repeats sequence"
    (is (= '(1 2 3 1 2 3 1) (eval* "(take 7 (cycle [1 2 3]))"))))
  (testing "cycle with small seq"
    (is (= '(:a :b :a :b :a) (eval* "(take 5 (cycle [:a :b]))")))))

(deftest repeatedly-test
  (testing "repeatedly with 0-arity fn"
    (is (= 5 (eval* "(count (take 5 (repeatedly (fn [] 42))))"))))
  (testing "repeatedly with n"
    (is (= 3 (eval* "(count (repeatedly 3 (fn [] :x)))")))))
