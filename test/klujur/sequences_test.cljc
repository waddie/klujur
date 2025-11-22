;; sequences_test.cljc - Tests for Klujur sequence operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.sequences-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Basic Sequence Access
;; =============================================================================

(deftest first-test
  (testing "first on various collections"
    (is (= 1 (eval* "(first [1 2 3])")))
    (is (= 1 (eval* "(first '(1 2 3))")))
    (is (= :a (eval* "(first [:a :b :c])"))))
  (testing "first on empty/nil"
    (is (nil? (eval* "(first [])")))
    (is (nil? (eval* "(first '())")))
    (is (nil? (eval* "(first nil)")))))

(deftest second-test
  (testing "second"
    (is (= 2 (eval* "(second [1 2 3])")))
    (is (= 2 (eval* "(second '(1 2 3))"))))
  (testing "second on short/empty"
    (is (nil? (eval* "(second [1])")))
    (is (nil? (eval* "(second [])")))
    (is (nil? (eval* "(second nil)")))))

(deftest last-test
  (testing "last"
    (is (= 3 (eval* "(last [1 2 3])")))
    (is (= 3 (eval* "(last '(1 2 3))"))))
  (testing "last on empty/nil"
    (is (nil? (eval* "(last [])")))
    (is (nil? (eval* "(last nil)")))))

(deftest rest-test
  (testing "rest returns remaining elements"
    (is (= '(2 3) (eval* "(rest [1 2 3])")))
    (is (= '(2 3) (eval* "(rest '(1 2 3))"))))
  (testing "rest on empty/nil returns empty seq"
    ;; IMPORTANT: rest returns () not nil
    (is (= '() (eval* "(rest [])")))
    (is (= '() (eval* "(rest '())")))
    (is (= '() (eval* "(rest nil)")))
    (is (= '() (eval* "(rest [1])")))))

(deftest next-test
  (testing "next returns remaining elements"
    (is (= '(2 3) (eval* "(next [1 2 3])")))
    (is (= '(2 3) (eval* "(next '(1 2 3))"))))
  (testing "next on empty/single returns nil"
    ;; IMPORTANT: next returns nil when exhausted
    (is (nil? (eval* "(next [])")))
    (is (nil? (eval* "(next '())")))
    (is (nil? (eval* "(next nil)")))
    (is (nil? (eval* "(next [1])")))))

;; =============================================================================
;; Nil Punning - Critical Clojure Semantics
;; =============================================================================
;; Adapted from Clojure's test_clojure/logic.clj test-nil-punning

(deftest nil-punning-test
  (testing "first on empty returns nil (falsy)"
    (is (nil? (eval* "(first [])")))
    (is (nil? (eval* "(first nil)"))))
  (testing "next on single element returns nil (falsy)"
    (is (nil? (eval* "(next [1])")))
    (is (nil? (eval* "(next '(1))"))))
  (testing "rest on single element returns () (truthy!)"
    ;; This is the critical difference: rest returns () which is truthy
    (is (= '() (eval* "(rest [1])")))
    (is (seq? (eval* "(rest [1])")))
    ;; () is truthy in conditionals
    (is (= :truthy (eval* "(if (rest [1]) :truthy :falsy)")))))

(deftest seq-nil-punning-test
  (testing "seq on empty collections returns nil"
    (is (nil? (eval* "(seq [])")))
    (is (nil? (eval* "(seq '())")))
    (is (nil? (eval* "(seq {})")))
    (is (nil? (eval* "(seq #{})")))
    (is (nil? (eval* "(seq nil)")))
    (is (nil? (eval* "(seq \"\")"))))
  (testing "seq on non-empty returns seq"
    (is (seq? (eval* "(seq [1 2 3])")))
    (is (seq? (eval* "(seq {:a 1})")))))

(deftest sequence-vs-seq-test
  (testing "sequence on empty returns () (truthy)"
    (is (= '() (eval* "(sequence [])")))
    ;; sequence returns () which is truthy
    (is (= :truthy (eval* "(if (sequence []) :truthy :falsy)"))))
  (testing "seq on empty returns nil (falsy)"
    (is (nil? (eval* "(seq [])")))
    (is (= :falsy (eval* "(if (seq []) :truthy :falsy)")))))

;; =============================================================================
;; cons
;; =============================================================================

(deftest cons-test
  (testing "cons adds to front"
    (is (= '(0 1 2 3) (eval* "(cons 0 [1 2 3])")))
    (is (= '(0 1 2 3) (eval* "(cons 0 '(1 2 3))"))))
  (testing "cons on nil" (is (= '(1) (eval* "(cons 1 nil)"))))
  (testing "cons always returns a seq"
    (is (seq? (eval* "(cons 1 [2 3])")))
    (is (seq? (eval* "(cons 1 nil)")))))

;; =============================================================================
;; conj (polymorphic)
;; =============================================================================

(deftest conj-polymorphic-test
  (testing "conj on nil creates list"
    (is (= '(1) (eval* "(conj nil 1)")))
    (is (list? (eval* "(conj nil 1)"))))
  (testing "conj preserves collection type"
    (is (vector? (eval* "(conj [] 1)")))
    (is (list? (eval* "(conj '() 1)")))
    (is (set? (eval* "(conj #{} 1)")))
    (is (map? (eval* "(conj {} [:a 1])")))))

;; =============================================================================
;; concat
;; =============================================================================

(deftest concat-test
  (testing "concat sequences"
    (is (= '(1 2 3 4) (eval* "(concat [1 2] [3 4])")))
    (is (= '(1 2 3 4) (eval* "(concat '(1 2) '(3 4))")))
    (is (= '(1 2 3 4 5 6) (eval* "(concat [1 2] [3 4] [5 6])"))))
  (testing "concat with empty/nil"
    (is (= '(1 2) (eval* "(concat [1 2] nil)")))
    (is (= '(1 2) (eval* "(concat nil [1 2])")))
    (is (= '() (eval* "(concat nil nil)")))))

;; =============================================================================
;; Sequence Transformations
;; =============================================================================

(deftest map-test
  (testing "map with single collection"
    (is (= '(2 3 4) (eval* "(map inc [1 2 3])")))
    (is (= '(2 4 6) (eval* "(map #(* % 2) [1 2 3])"))))
  (testing "map with multiple collections"
    (is (= '(5 7 9) (eval* "(map + [1 2 3] [4 5 6])")))
    (is (= '([1 4] [2 5] [3 6]) (eval* "(map vector [1 2 3] [4 5 6])"))))
  (testing "map returns lazy seq" (is (seq? (eval* "(map inc [1 2 3])")))))

(deftest filter-test
  (testing "filter"
    (is (= '(2 4) (eval* "(filter even? [1 2 3 4])")))
    (is (= '(1 3) (eval* "(filter odd? [1 2 3 4])")))
    (is (= '() (eval* "(filter even? [1 3 5])")))))

(deftest remove-test
  (testing "remove (inverse of filter)"
    (is (= '(1 3) (eval* "(remove even? [1 2 3 4])")))
    (is (= '(2 4) (eval* "(remove odd? [1 2 3 4])")))))

(deftest reduce-test
  (testing "reduce with initial value"
    (is (= 10 (eval* "(reduce + 0 [1 2 3 4])")))
    (is (= 24 (eval* "(reduce * 1 [1 2 3 4])"))))
  (testing "reduce without initial value"
    (is (= 10 (eval* "(reduce + [1 2 3 4])")))
    (is (= 6 (eval* "(reduce + [1 2 3])"))))
  (testing "reduce on empty collection"
    (is (= 0 (eval* "(reduce + 0 [])")))
    (is (= 0 (eval* "(reduce + [])")))))  ; + with no args is 0

(deftest take-test
  (testing "take"
    (is (= '(1 2 3) (eval* "(take 3 [1 2 3 4 5])")))
    (is (= '(1 2) (eval* "(take 2 [1 2 3])")))
    (is (= '() (eval* "(take 0 [1 2 3])")))
    (is (= '(1 2 3) (eval* "(take 10 [1 2 3])")))))  ; takes available

(deftest drop-test
  (testing "drop"
    (is (= '(4 5) (eval* "(drop 3 [1 2 3 4 5])")))
    (is (= '(3) (eval* "(drop 2 [1 2 3])")))
    (is (= '(1 2 3) (eval* "(drop 0 [1 2 3])")))
    (is (= '() (eval* "(drop 10 [1 2 3])")))))

(deftest take-while-test
  (testing "take-while"
    (is (= '(1 2 3) (eval* "(take-while #(< % 4) [1 2 3 4 5])")))
    (is (= '() (eval* "(take-while even? [1 2 3])")))))

(deftest drop-while-test
  (testing "drop-while"
    (is (= '(4 5) (eval* "(drop-while #(< % 4) [1 2 3 4 5])")))
    (is (= '(1 2 3) (eval* "(drop-while even? [1 2 3])")))))

(deftest partition-test
  (testing "partition"
    (is (= '((1 2) (3 4)) (eval* "(partition 2 [1 2 3 4])")))
    (is (= '((1 2) (3 4)) (eval* "(partition 2 [1 2 3 4 5])"))) ; drops
                                                                ; incomplete
    (is (= '((1 2 3) (4 5 6)) (eval* "(partition 3 [1 2 3 4 5 6])")))))

(deftest partition-all-test
  (testing "partition-all (includes incomplete)"
    (is (= '((1 2) (3 4) (5)) (eval* "(partition-all 2 [1 2 3 4 5])")))))

(deftest partition-by-test
  (testing "partition-by"
    (is (= '((1 1) (2 2) (3 3))
           (eval* "(partition-by identity [1 1 2 2 3 3])")))
    (is (= '((1 3) (2 4) (5)) (eval* "(partition-by even? [1 3 2 4 5])")))))

(deftest interleave-test
  (testing "interleave"
    (is (= '(1 :a 2 :b 3 :c) (eval* "(interleave [1 2 3] [:a :b :c])")))
    (is (= '(1 :a 2 :b) (eval* "(interleave [1 2 3] [:a :b])")))))  ; stops at shortest

(deftest interpose-test
  (testing "interpose"
    (is (= '(1 :sep 2 :sep 3) (eval* "(interpose :sep [1 2 3])")))
    (is (= '(1) (eval* "(interpose :sep [1])")))
    (is (= '() (eval* "(interpose :sep [])")))))

(deftest reverse-test
  (testing "reverse"
    (is (= '(3 2 1) (eval* "(reverse [1 2 3])")))
    (is (= '(3 2 1) (eval* "(reverse '(1 2 3))")))
    (is (= '() (eval* "(reverse [])")))))

(deftest sort-test
  (testing "sort"
    (is (= '(1 2 3 4 5) (eval* "(sort [3 1 4 1 5 2])")))
    (is (= '(1 2 3) (eval* "(sort [3 2 1])"))))
  (testing "sort with comparator"
    (is (= '(5 4 3 2 1) (eval* "(sort > [1 2 3 4 5])")))))

(deftest sort-by-test
  (testing "sort-by"
    (is (= '("a" "bb" "ccc") (eval* "(sort-by count [\"ccc\" \"a\" \"bb\"])")))
    (is (= '({:x 1} {:x 2} {:x 3})
           (eval* "(sort-by :x [{:x 2} {:x 1} {:x 3}])")))))

(deftest flatten-test
  (testing "flatten"
    (is (= '(1 2 3 4) (eval* "(flatten [[1 2] [3 4]])")))
    (is (= '(1 2 3 4 5 6) (eval* "(flatten [[1 [2 3]] [[4] 5] 6])")))
    (is (= '(1 2 3) (eval* "(flatten [1 2 3])")))))

(deftest distinct-test
  (testing "distinct"
    (is (= '(1 2 3) (eval* "(distinct [1 1 2 2 3 3])")))
    (is (= '(1 2 3) (eval* "(distinct [1 2 3 1 2])")))))

(deftest dedupe-test
  (testing "dedupe (removes consecutive duplicates)"
    (is (= '(1 2 3 2 1) (eval* "(dedupe [1 1 2 2 3 3 2 2 1 1])")))
    (is (= '(1 2 3) (eval* "(dedupe [1 1 1 2 2 2 3 3 3])")))))

;; =============================================================================
;; Sequence Predicates
;; =============================================================================

(deftest every-test
  (testing "every?"
    (is (true? (eval* "(every? even? [2 4 6])")))
    (is (false? (eval* "(every? even? [2 3 4])")))
    (is (true? (eval* "(every? even? [])")))))  ; vacuous truth

(deftest some-test
  (testing "some"
    (is (true? (eval* "(some even? [1 2 3])"))) ; returns truthy value
    (is (nil? (eval* "(some even? [1 3 5])")))
    (is (= 2 (eval* "(some #(when (even? %) %) [1 2 3])")))))

(deftest not-every-test
  (testing "not-every?"
    (is (true? (eval* "(not-every? even? [1 2 3])")))
    (is (false? (eval* "(not-every? even? [2 4 6])")))))

(deftest not-any-test
  (testing "not-any?"
    (is (true? (eval* "(not-any? even? [1 3 5])")))
    (is (false? (eval* "(not-any? even? [1 2 3])")))))

;; =============================================================================
;; Infinite/Lazy Sequences
;; =============================================================================

(deftest range-test
  (testing "range"
    (is (= '(0 1 2 3 4) (eval* "(range 5)")))
    (is (= '(1 2 3 4) (eval* "(range 1 5)")))
    (is (= '(0 2 4 6 8) (eval* "(range 0 10 2)"))))
  (testing "range is lazy"
    ;; Taking from infinite range
    (is (= '(0 1 2 3 4) (eval* "(take 5 (range))")))))

(deftest repeat-test
  (testing "repeat with count" (is (= '(:a :a :a) (eval* "(repeat 3 :a)"))))
  (testing "infinite repeat (take limited)"
    (is (= '(:x :x :x :x :x) (eval* "(take 5 (repeat :x))")))))

(deftest repeatedly-test
  (testing "repeatedly with count"
    ;; Note: repeatedly calls fn each time
    (is (= 5 (count (eval* "(repeatedly 5 #(rand-int 10))"))))))

(deftest iterate-test
  (testing "iterate"
    (is (= '(1 2 4 8 16) (eval* "(take 5 (iterate #(* % 2) 1))")))
    (is (= '(0 1 2 3 4) (eval* "(take 5 (iterate inc 0))")))))

(deftest cycle-test
  (testing "cycle"
    (is (= '(1 2 3 1 2 3 1) (eval* "(take 7 (cycle [1 2 3]))")))))

;; =============================================================================
;; Sequence Utilities
;; =============================================================================

(deftest butlast-test
  (testing "butlast"
    (is (= '(1 2) (eval* "(butlast [1 2 3])")))
    (is (nil? (eval* "(butlast [1])")))
    (is (nil? (eval* "(butlast [])")))))

(deftest nthnext-test
  (testing "nthnext"
    (is (= '(3 4 5) (eval* "(nthnext [1 2 3 4 5] 2)")))
    (is (nil? (eval* "(nthnext [1 2] 5)")))))

(deftest nthrest-test
  (testing "nthrest"
    (is (= '(3 4 5) (eval* "(nthrest [1 2 3 4 5] 2)")))
    (is (= '() (eval* "(nthrest [1 2] 5)")))))  ; returns () not nil

(deftest split-at-test
  (testing "split-at"
    (is (= ['(1 2) '(3 4 5)] (eval* "(split-at 2 [1 2 3 4 5])")))))

(deftest split-with-test
  (testing "split-with"
    (is (= ['(1 2 3) '(4 5)] (eval* "(split-with #(< % 4) [1 2 3 4 5])")))))

(deftest group-by-test
  (testing "group-by"
    (is (= {true [2 4] false [1 3 5]} (eval* "(group-by even? [1 2 3 4 5])")))
    (is
     (= {3 ["the" "fox"] 5 ["quick" "brown" "jumps"]}
        (eval*
         "(group-by count [\"the\" \"quick\" \"brown\" \"fox\" \"jumps\"])")))))

(deftest frequencies-test
  (testing "frequencies"
    (is (= {:a 3 :b 2 :c 1} (eval* "(frequencies [:a :a :a :b :b :c])")))))

(deftest zipmap-test
  (testing "zipmap"
    (is (= {:a 1 :b 2 :c 3} (eval* "(zipmap [:a :b :c] [1 2 3])")))
    (is (= {:a 1 :b 2} (eval* "(zipmap [:a :b :c] [1 2])")))))  ; stops at shorter

;; =============================================================================
;; mapcat, keep, etc.
;; =============================================================================

(deftest mapcat-test
  (testing "mapcat"
    (is (= '(1 2 2 3 3 3) (eval* "(mapcat #(repeat % %) [1 2 3])")))
    (is (= '(:a 1 :b 2) (eval* "(mapcat identity [[:a 1] [:b 2]])")))))

(deftest keep-test
  (testing "keep (removes nils)"
    (is (= '(2 4) (eval* "(keep #(when (even? %) %) [1 2 3 4 5])")))
    (is (= '(false) (eval* "(keep #(when (= % 0) false) [0 1 2])")))))  ; keeps false

(deftest keep-indexed-test
  (testing "keep-indexed"
    (is (= '(0 2 4)
           (eval* "(keep-indexed #(when (even? %1) %2) [:a :b :c :d :e])")))))

(deftest map-indexed-test
  (testing "map-indexed"
    (is (= '([0 :a] [1 :b] [2 :c]) (eval* "(map-indexed vector [:a :b :c])")))))
