;; sequences_test.cljc - Tests for Klujur sequence operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.sequences-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Basic Sequence Access
;; =============================================================================

(deftest first-test
  (testing "first on various collections"
    (is (= 1 (first [1 2 3])))
    (is (= 1 (first '(1 2 3))))
    (is (= :a (first [:a :b :c]))))
  (testing "first on empty/nil"
    (is (nil? (first [])))
    (is (nil? (first '())))
    (is (nil? (first nil)))))

(deftest second-test
  (testing "second" (is (= 2 (second [1 2 3]))) (is (= 2 (second '(1 2 3)))))
  (testing "second on short/empty"
    (is (nil? (second [1])))
    (is (nil? (second [])))
    (is (nil? (second nil)))))

(deftest last-test
  (testing "last" (is (= 3 (last [1 2 3]))) (is (= 3 (last '(1 2 3)))))
  (testing "last on empty/nil" (is (nil? (last []))) (is (nil? (last nil)))))

(deftest rest-test
  (testing "rest returns remaining elements"
    (is (= '(2 3) (rest [1 2 3])))
    (is (= '(2 3) (rest '(1 2 3)))))
  (testing "rest on empty/nil returns empty seq"
    ;; IMPORTANT: rest returns () not nil
    (is (= '() (rest [])))
    (is (= '() (rest '())))
    (is (= '() (rest nil)))
    (is (= '() (rest [1])))))

(deftest next-test
  (testing "next returns remaining elements"
    (is (= '(2 3) (next [1 2 3])))
    (is (= '(2 3) (next '(1 2 3)))))
  (testing "next on empty/single returns nil"
    ;; IMPORTANT: next returns nil when exhausted
    (is (nil? (next [])))
    (is (nil? (next '())))
    (is (nil? (next nil)))
    (is (nil? (next [1])))))

;; =============================================================================
;; Nil Punning - Critical Clojure Semantics
;; =============================================================================
;; Adapted from Clojure's test_clojure/logic.clj test-nil-punning

(deftest nil-punning-test
  (testing "first on empty returns nil (falsy)"
    (is (nil? (first [])))
    (is (nil? (first nil))))
  (testing "next on single element returns nil (falsy)"
    (is (nil? (next [1])))
    (is (nil? (next '(1)))))
  (testing "rest on single element returns () (truthy!)"
    ;; This is the critical difference: rest returns () which is truthy
    (is (= '() (rest [1])))
    (is (seq? (rest [1])))
    ;; () is truthy in conditionals
    (is (= :truthy (if (rest [1]) :truthy :falsy)))))

(deftest seq-nil-punning-test
  (testing "seq on empty collections returns nil"
    (is (nil? (seq [])))
    (is (nil? (seq '())))
    (is (nil? (seq {})))
    (is (nil? (seq #{})))
    (is (nil? (seq nil)))
    (is (nil? (seq ""))))
  (testing "seq on non-empty returns seq"
    (is (seq? (seq [1 2 3])))
    (is (seq? (seq {:a 1})))))

(deftest sequence-vs-seq-test
  (testing "sequence on empty returns () (truthy)"
    (is (= '() (sequence [])))
    ;; sequence returns () which is truthy
    (is (= :truthy (if (sequence []) :truthy :falsy))))
  (testing "seq on empty returns nil (falsy)"
    (is (nil? (seq [])))
    (is (= :falsy (if (seq []) :truthy :falsy)))))

;; =============================================================================
;; cons
;; =============================================================================

(deftest cons-test
  (testing "cons adds to front"
    (is (= '(0 1 2 3) (cons 0 [1 2 3])))
    (is (= '(0 1 2 3) (cons 0 '(1 2 3)))))
  (testing "cons on nil" (is (= '(1) (cons 1 nil))))
  (testing "cons always returns a seq"
    (is (seq? (cons 1 [2 3])))
    (is (seq? (cons 1 nil)))))

;; =============================================================================
;; conj (polymorphic)
;; =============================================================================

(deftest conj-polymorphic-test
  (testing "conj on nil creates list"
    (is (= '(1) (conj nil 1)))
    (is (list? (conj nil 1))))
  (testing "conj preserves collection type"
    (is (vector? (conj [] 1)))
    (is (list? (conj '() 1)))
    (is (set? (conj #{} 1)))
    (is (map? (conj {} [:a 1])))))

;; =============================================================================
;; concat
;; =============================================================================

(deftest concat-test
  (testing "concat sequences"
    (is (= '(1 2 3 4) (concat [1 2] [3 4])))
    (is (= '(1 2 3 4) (concat '(1 2) '(3 4))))
    (is (= '(1 2 3 4 5 6) (concat [1 2] [3 4] [5 6]))))
  (testing "concat with empty/nil"
    (is (= '(1 2) (concat [1 2] nil)))
    (is (= '(1 2) (concat nil [1 2])))
    (is (= '() (concat nil nil)))))

;; =============================================================================
;; Sequence Transformations
;; =============================================================================

(deftest map-test
  (testing "map with single collection"
    (is (= '(2 3 4) (map inc [1 2 3])))
    (is (= '(2 4 6) (map #(* % 2) [1 2 3]))))
  (testing "map with multiple collections"
    (is (= '(5 7 9) (map + [1 2 3] [4 5 6])))
    (is (= '([1 4] [2 5] [3 6]) (map vector [1 2 3] [4 5 6]))))
  (testing "map returns lazy seq" (is (seq? (map inc [1 2 3])))))

(deftest filter-test
  (testing "filter"
    (is (= '(2 4) (filter even? [1 2 3 4])))
    (is (= '(1 3) (filter odd? [1 2 3 4])))
    (is (= '() (filter even? [1 3 5])))))

(deftest remove-test
  (testing "remove (inverse of filter)"
    (is (= '(1 3) (remove even? [1 2 3 4])))
    (is (= '(2 4) (remove odd? [1 2 3 4])))))

(deftest reduce-test
  (testing "reduce with initial value"
    (is (= 10 (reduce + 0 [1 2 3 4])))
    (is (= 24 (reduce * 1 [1 2 3 4]))))
  (testing "reduce without initial value"
    (is (= 10 (reduce + [1 2 3 4])))
    (is (= 6 (reduce + [1 2 3]))))
  (testing "reduce on empty collection"
    (is (= 0 (reduce + 0 [])))
    (is (= 0 (reduce + [])))))  ; + with no args is 0

(deftest take-test
  (testing "take"
    (is (= '(1 2 3) (take 3 [1 2 3 4 5])))
    (is (= '(1 2) (take 2 [1 2 3])))
    (is (= '() (take 0 [1 2 3])))
    (is (= '(1 2 3) (take 10 [1 2 3])))))  ; takes available

(deftest drop-test
  (testing "drop"
    (is (= '(4 5) (drop 3 [1 2 3 4 5])))
    (is (= '(3) (drop 2 [1 2 3])))
    (is (= '(1 2 3) (drop 0 [1 2 3])))
    (is (= '() (drop 10 [1 2 3])))))

;; =============================================================================
;; Negative Argument Edge Cases (take/drop)
;; =============================================================================

(deftest take-negative-args-test
  (testing "take with negative n"
    ;; In Clojure, (take -1 coll) returns empty seq, not an error
    (is (= '() (take -1 [1 2 3])))
    (is (= '() (take -5 [1 2 3])))
    (is (= '() (take -1 [])))))

(deftest drop-negative-args-test
  (testing "drop with negative n"
    ;; In Clojure, (drop -1 coll) returns the entire collection
    (is (= '(1 2 3) (drop -1 [1 2 3])))
    (is (= '(1 2 3) (drop -5 [1 2 3])))
    (is (= '() (drop -1 [])))))

(deftest take-while-test
  (testing "take-while"
    (is (= '(1 2 3) (take-while #(< % 4) [1 2 3 4 5])))
    (is (= '() (take-while even? [1 2 3])))))

(deftest drop-while-test
  (testing "drop-while"
    (is (= '(4 5) (drop-while #(< % 4) [1 2 3 4 5])))
    (is (= '(1 2 3) (drop-while even? [1 2 3])))))

(deftest partition-test
  (testing "partition"
    (is (= '((1 2) (3 4)) (partition 2 [1 2 3 4])))
    (is (= '((1 2) (3 4)) (partition 2 [1 2 3 4 5]))) ; drops incomplete
    (is (= '((1 2 3) (4 5 6)) (partition 3 [1 2 3 4 5 6])))))

(deftest partition-all-test
  (testing "partition-all (includes incomplete)"
    (is (= '((1 2) (3 4) (5)) (partition-all 2 [1 2 3 4 5])))))

(deftest partition-by-test
  (testing "partition-by"
    (is (= '((1 1) (2 2) (3 3)) (partition-by identity [1 1 2 2 3 3])))
    (is (= '((1 3) (2 4) (5)) (partition-by even? [1 3 2 4 5])))))

(deftest interleave-test
  (testing "interleave"
    (is (= '(1 :a 2 :b 3 :c) (interleave [1 2 3] [:a :b :c])))
    (is (= '(1 :a 2 :b) (interleave [1 2 3] [:a :b])))))  ; stops at shortest

(deftest interpose-test
  (testing "interpose"
    (is (= '(1 :sep 2 :sep 3) (interpose :sep [1 2 3])))
    (is (= '(1) (interpose :sep [1])))
    (is (= '() (interpose :sep [])))))

(deftest reverse-test
  (testing "reverse"
    (is (= '(3 2 1) (reverse [1 2 3])))
    (is (= '(3 2 1) (reverse '(1 2 3))))
    (is (= '() (reverse [])))))

(deftest sort-test
  (testing "sort"
    (is (= '(1 2 3 4 5) (sort [3 1 4 1 5 2])))
    (is (= '(1 2 3) (sort [3 2 1]))))
  (testing "sort with comparator" (is (= '(5 4 3 2 1) (sort > [1 2 3 4 5])))))

(deftest sort-by-test
  (testing "sort-by"
    (is (= '("a" "bb" "ccc") (sort-by count ["ccc" "a" "bb"])))
    (is (= '({:x 1} {:x 2} {:x 3}) (sort-by :x [{:x 2} {:x 1} {:x 3}])))))

(deftest flatten-test
  (testing "flatten"
    (is (= '(1 2 3 4) (flatten [[1 2] [3 4]])))
    (is (= '(1 2 3 4 5 6) (flatten [[1 [2 3]] [[4] 5] 6])))
    (is (= '(1 2 3) (flatten [1 2 3])))))

(deftest distinct-test
  (testing "distinct"
    (is (= '(1 2 3) (distinct [1 1 2 2 3 3])))
    (is (= '(1 2 3) (distinct [1 2 3 1 2])))))

(deftest dedupe-test
  (testing "dedupe (removes consecutive duplicates)"
    (is (= '(1 2 3 2 1) (dedupe [1 1 2 2 3 3 2 2 1 1])))
    (is (= '(1 2 3) (dedupe [1 1 1 2 2 2 3 3 3])))))

;; =============================================================================
;; Sequence Predicates
;; =============================================================================

(deftest every-test
  (testing "every?"
    (is (true? (every? even? [2 4 6])))
    (is (false? (every? even? [2 3 4])))
    (is (true? (every? even? [])))))  ; vacuous truth

(deftest some-test
  (testing "some"
    (is (true? (some even? [1 2 3]))) ; returns truthy value
    (is (nil? (some even? [1 3 5])))
    (is (= 2 (some #(when (even? %) %) [1 2 3])))))

(deftest not-every-test
  (testing "not-every?"
    (is (true? (not-every? even? [1 2 3])))
    (is (false? (not-every? even? [2 4 6])))))

(deftest not-any-test
  (testing "not-any?"
    (is (true? (not-any? even? [1 3 5])))
    (is (false? (not-any? even? [1 2 3])))))

;; =============================================================================
;; Infinite/Lazy Sequences
;; =============================================================================

(deftest range-test
  (testing "range"
    (is (= '(0 1 2 3 4) (range 5)))
    (is (= '(1 2 3 4) (range 1 5)))
    (is (= '(0 2 4 6 8) (range 0 10 2))))
  (testing "range is lazy"
    ;; Taking from infinite range
    (is (= '(0 1 2 3 4) (take 5 (range))))))

(deftest repeat-test
  (testing "repeat with count" (is (= '(:a :a :a) (repeat 3 :a))))
  (testing "infinite repeat (take limited)"
    (is (= '(:x :x :x :x :x) (take 5 (repeat :x))))))

(deftest repeatedly-test
  (testing "repeatedly with count"
    ;; Note: repeatedly calls fn each time
    (is (= 5 (count (repeatedly 5 #(rand-int 10)))))))

(deftest iterate-test
  (testing "iterate"
    (is (= '(1 2 4 8 16) (take 5 (iterate #(* % 2) 1))))
    (is (= '(0 1 2 3 4) (take 5 (iterate inc 0))))))

(deftest cycle-test
  (testing "cycle" (is (= '(1 2 3 1 2 3 1) (take 7 (cycle [1 2 3]))))))

;; =============================================================================
;; Sequence Utilities
;; =============================================================================

(deftest butlast-test
  (testing "butlast"
    (is (= '(1 2) (butlast [1 2 3])))
    (is (nil? (butlast [1])))
    (is (nil? (butlast [])))))

(deftest nthnext-test
  (testing "nthnext"
    (is (= '(3 4 5) (nthnext [1 2 3 4 5] 2)))
    (is (nil? (nthnext [1 2] 5)))))

(deftest nthrest-test
  (testing "nthrest"
    (is (= '(3 4 5) (nthrest [1 2 3 4 5] 2)))
    (is (= '() (nthrest [1 2] 5)))))  ; returns () not nil

(deftest split-at-test
  (testing "split-at" (is (= ['(1 2) '(3 4 5)] (split-at 2 [1 2 3 4 5])))))

(deftest split-with-test
  (testing "split-with"
    (is (= ['(1 2 3) '(4 5)] (split-with #(< % 4) [1 2 3 4 5])))))

(deftest group-by-test
  (testing "group-by"
    (is (= {true [2 4] false [1 3 5]} (group-by even? [1 2 3 4 5])))
    (is (= {3 ["the" "fox"] 5 ["quick" "brown" "jumps"]}
           (group-by count ["the" "quick" "brown" "fox" "jumps"])))))

(deftest frequencies-test
  (testing "frequencies"
    (is (= {:a 3 :b 2 :c 1} (frequencies [:a :a :a :b :b :c])))))

(deftest zipmap-test
  (testing "zipmap"
    (is (= {:a 1 :b 2 :c 3} (zipmap [:a :b :c] [1 2 3])))
    (is (= {:a 1 :b 2} (zipmap [:a :b :c] [1 2])))))  ; stops at shorter

;; =============================================================================
;; mapcat, keep, etc.
;; =============================================================================

(deftest mapcat-test
  (testing "mapcat"
    (is (= '(1 2 2 3 3 3) (mapcat #(repeat % %) [1 2 3])))
    (is (= '(:a 1 :b 2) (mapcat identity [[:a 1] [:b 2]])))))

(deftest keep-test
  (testing "keep (removes nils)"
    (is (= '(2 4) (keep #(when (even? %) %) [1 2 3 4 5])))
    (is (= '(false) (keep #(when (= % 0) false) [0 1 2])))))  ; keeps false

(deftest keep-indexed-test
  (testing "keep-indexed"
    (is (= '(0 2 4) (keep-indexed #(when (even? %1) %2) [:a :b :c :d :e])))))

(deftest map-indexed-test
  (testing "map-indexed"
    (is (= '([0 :a] [1 :b] [2 :c]) (map-indexed vector [:a :b :c])))))

;; =============================================================================
;; run! - Eager side-effect iteration
;; =============================================================================

(deftest run!-test
  (testing "run! executes side effects"
    ;; run! should iterate and call proc for each element
    (is (= [1 2 3]
           (do (def side-effects (atom []))
               (run! #(swap! side-effects conj %) [1 2 3])
               @side-effects))))
  (testing "run! returns nil"
    (is (nil? (run! identity [1 2 3])))
    (is (nil? (run! inc [])))))

;; =============================================================================
;; trampoline - Tail-call optimisation helper
;; =============================================================================

(deftest trampoline-test
  (testing "trampoline with non-fn return"
    (is (= 42 (trampoline (constantly 42)))))
  (testing "trampoline with fn chain"
    (is (= "done!"
           (do (defn countdown [n] (if (zero? n) "done!" #(countdown (dec n))))
               (trampoline countdown 5)))))
  (testing "trampoline with args" (is (= 10 (trampoline + 1 2 3 4))))
  (testing "trampoline enables mutual recursion"
    (is (= true
           (do (defn my-even? [n] (if (zero? n) true #(my-odd? (dec n))))
               (defn my-odd? [n] (if (zero? n) false #(my-even? (dec n))))
               (trampoline my-even? 10))))
    (is (= false (trampoline my-odd? 10)))))

;; =============================================================================
;; tree-seq - Lazy tree traversal
;; =============================================================================

(deftest tree-seq-test
  (testing "tree-seq on nested lists"
    (is (= '(((1 2 (3)) (4)) (1 2 (3)) 1 2 (3) 3 (4) 4)
           (doall (tree-seq seq? identity '((1 2 (3)) (4)))))))
  (testing "tree-seq on nested vectors"
    (is (= '([[1 2 [3]] [4]] [1 2 [3]] 1 2 [3] 3 [4] 4)
           (doall (tree-seq vector? seq [[1 2 [3]] [4]])))))
  (testing "tree-seq on single non-branch node"
    (is (= '(5) (doall (tree-seq seq? identity 5)))))
  (testing "tree-seq returns lazy sequence"
    (is (seq? (tree-seq seq? identity '(1 2 3))))))

;; =============================================================================
;; random-sample - Probabilistic filtering
;; =============================================================================

(deftest random-sample-test
  (testing "random-sample with prob 1.0 keeps all"
    (is (= '(1 2 3 4 5) (doall (random-sample 1.0 [1 2 3 4 5])))))
  (testing "random-sample with prob 0.0 keeps none"
    (is (= '() (doall (random-sample 0.0 [1 2 3 4 5])))))
  (testing "random-sample returns subset"
    ;; With 0.5 probability, result should be between 0 and 100 elements
    (is (<= 0 (count (random-sample 0.5 (range 100))) 100)))
  (testing "random-sample as transducer"
    (is (<= 0 (count (into [] (random-sample 0.5) (range 100))) 100))))

;; =============================================================================
;; halt-when - Early termination transducer
;; =============================================================================

(deftest halt-when-test
  (testing "halt-when stops and returns triggering input"
    (is (= 5 (into [] (halt-when #(= % 5)) (range 10)))))
  (testing "halt-when with retf"
    (is (= [0 1 2 3 4 :stopped-at 5]
           (into []
                 (halt-when #(= % 5) (fn [r x] (conj r :stopped-at x)))
                 (range 10)))))
  (testing "halt-when completes normally if pred never true"
    (is (= [0 1 2 3 4 5 6 7 8 9] (into [] (halt-when #(= % 100)) (range 10)))))
  (testing "halt-when works with transduce"
    (is (= 5 (transduce (halt-when #(> % 4)) conj [] (range 10))))))

(run-all-tests)
