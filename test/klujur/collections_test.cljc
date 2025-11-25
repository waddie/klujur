;; collections_test.cljc - Tests for Klujur collection operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.collections-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Lists
;; =============================================================================

(deftest list-creation-test
  (testing "list function"
    (is (= '() (list)))
    (is (= '(1) (list 1)))
    (is (= '(1 2 3) (list 1 2 3))))
  (testing "list evaluates arguments"
    (is (= '(2 4 6) (list (+ 1 1) (+ 2 2) (+ 3 3))))))

(deftest list-predicate-test
  (testing "list?"
    (is (true? (list? '())))
    (is (true? (list? '(1 2 3))))
    (is (true? (list? (list 1 2))))
    (is (false? (list? [])))
    (is (false? (list? nil)))))

(deftest list-count-test
  (testing "count on list"
    (is (= 0 (count '())))
    (is (= 1 (count '(1))))
    (is (= 3 (count '(1 2 3))))))

(deftest list-nth-test
  (testing "nth on list"
    (is (= 1 (nth '(1 2 3) 0)))
    (is (= 2 (nth '(1 2 3) 1)))
    (is (= 3 (nth '(1 2 3) 2))))
  (testing "nth with not-found" (is (= :default (nth '(1 2) 5 :default))))
  (testing "nth out of bounds" (is (thrown? Exception (nth '(1 2) 5)))))

(deftest list-peek-pop-test
  (testing "peek on list (returns first)"
    (is (= 1 (peek '(1 2 3))))
    (is (nil? (peek '()))))
  (testing "pop on list (removes first)"
    (is (= '(2 3) (pop '(1 2 3))))
    (is (thrown? Exception (pop '())))))

(deftest list-conj-test
  (testing "conj on list (adds to front)"
    (is (= '(0 1 2 3) (conj '(1 2 3) 0)))
    (is (= '(1) (conj '() 1)))
    (is (= '(-1 0 1 2 3) (conj '(1 2 3) 0 -1)))))

;; =============================================================================
;; Vectors
;; =============================================================================

(deftest vector-creation-test
  (testing "vector function"
    (is (= [] (vector)))
    (is (= [1] (vector 1)))
    (is (= [1 2 3] (vector 1 2 3))))
  (testing "vec function"
    (is (= [1 2 3] (vec '(1 2 3))))
    (is (= [1 2 3] (vec [1 2 3])))
    (is (= [] (vec nil)))))

(deftest vector-predicate-test
  (testing "vector?"
    (is (true? (vector? [])))
    (is (true? (vector? [1 2 3])))
    (is (false? (vector? '(1 2 3))))
    (is (false? (vector? nil)))))

(deftest vector-count-test
  (testing "count on vector"
    (is (= 0 (count [])))
    (is (= 1 (count [1])))
    (is (= 3 (count [1 2 3])))))

(deftest vector-nth-test
  (testing "nth on vector"
    (is (= 1 (nth [1 2 3] 0)))
    (is (= 2 (nth [1 2 3] 1)))
    (is (= 3 (nth [1 2 3] 2))))
  (testing "nth with not-found" (is (= :default (nth [1 2] 5 :default))))
  (testing "nth out of bounds" (is (thrown? Exception (nth [1 2] 5)))))

(deftest vector-get-test
  (testing "get on vector"
    (is (= 1 (get [1 2 3] 0)))
    (is (= 2 (get [1 2 3] 1)))
    (is (nil? (get [1 2 3] 5))))
  (testing "get with not-found" (is (= :default (get [1 2] 5 :default)))))

(deftest vector-peek-pop-test
  (testing "peek on vector (returns last)"
    (is (= 3 (peek [1 2 3])))
    (is (nil? (peek []))))
  (testing "pop on vector (removes last)"
    (is (= [1 2] (pop [1 2 3])))
    (is (thrown? Exception (pop [])))))

(deftest vector-conj-test
  (testing "conj on vector (adds to end)"
    (is (= [1 2 3 4] (conj [1 2 3] 4)))
    (is (= [1] (conj [] 1)))
    (is (= [1 2 3 4 5] (conj [1 2 3] 4 5)))))

(deftest vector-assoc-test
  (testing "assoc on vector"
    (is (= [1 :x 3] (assoc [1 2 3] 1 :x)))
    (is (= [:a 2 3] (assoc [1 2 3] 0 :a)))
    (is (= [1 2 :c] (assoc [1 2 3] 2 :c)))))

(deftest vector-subvec-test
  (testing "subvec"
    (is (= [2 3] (subvec [1 2 3 4] 1 3)))
    (is (= [2 3 4] (subvec [1 2 3 4] 1)))
    (is (= [] (subvec [1 2 3] 2 2)))))

(deftest vector-as-function-test
  (testing "vector as function (lookup)"
    (is (= :b ([:a :b :c] 1)))
    ;; Out of bounds throws, unlike get which returns nil
    (is (thrown? Exception ([:a :b] 5)))))

;; =============================================================================
;; Maps
;; =============================================================================

(deftest map-creation-test
  (testing "hash-map function"
    (is (= {} (hash-map)))
    (is (= {:a 1} (hash-map :a 1)))
    (is (= {:a 1 :b 2} (hash-map :a 1 :b 2))))
  (testing "array-map function"
    (is (= {} (array-map)))
    (is (= {:a 1 :b 2} (array-map :a 1 :b 2)))))

(deftest map-predicate-test
  (testing "map?"
    (is (true? (map? {})))
    (is (true? (map? {:a 1})))
    (is (false? (map? [])))
    (is (false? (map? nil)))))

(deftest map-count-test
  (testing "count on map"
    (is (= 0 (count {})))
    (is (= 1 (count {:a 1})))
    (is (= 2 (count {:a 1 :b 2})))))

(deftest map-get-test
  (testing "get on map"
    (is (= 1 (get {:a 1 :b 2} :a)))
    (is (= 2 (get {:a 1 :b 2} :b)))
    (is (nil? (get {:a 1} :c))))
  (testing "get with not-found" (is (= :default (get {:a 1} :c :default)))))

(deftest map-as-function-test
  (testing "map as function (lookup)"
    (is (= 1 ({:a 1 :b 2} :a)))
    (is (= 2 ({:a 1 :b 2} :b)))
    (is (nil? ({:a 1} :c)))
    (is (= :default ({:a 1} :c :default)))))

(deftest keyword-as-function-test
  (testing "keyword as function (lookup)"
    (is (= 1 (:a {:a 1 :b 2})))
    (is (= 2 (:b {:a 1 :b 2})))
    (is (nil? (:c {:a 1})))
    (is (= :default (:c {:a 1} :default)))))

(deftest map-assoc-test
  (testing "assoc on map"
    (is (= {:a 1 :b 2} (assoc {:a 1} :b 2)))
    (is (= {:a 10} (assoc {:a 1} :a 10))) ; replace
    (is (= {:a 1 :b 2 :c 3} (assoc {:a 1} :b 2 :c 3)))))

(deftest map-dissoc-test
  (testing "dissoc on map"
    (is (= {:b 2} (dissoc {:a 1 :b 2} :a)))
    (is (= {} (dissoc {:a 1} :a)))
    (is (= {:a 1} (dissoc {:a 1} :b))) ; key not present
    (is (= {} (dissoc {:a 1 :b 2} :a :b)))))

(deftest map-keys-vals-test
  (testing "keys"
    (is (= #{:a :b} (set (keys {:a 1 :b 2}))))
    (is (nil? (keys {}))))
  (testing "vals"
    (is (= #{1 2} (set (vals {:a 1 :b 2}))))
    (is (nil? (vals {})))))

(deftest map-contains-test
  (testing "contains?"
    (is (true? (contains? {:a 1} :a)))
    (is (false? (contains? {:a 1} :b)))
    (is (true? (contains? {:a nil} :a)))) ; nil value, key exists
  (testing "contains? on vector (index check)"
    (is (true? (contains? [1 2 3] 0)))
    (is (true? (contains? [1 2 3] 2)))
    (is (false? (contains? [1 2 3] 3)))))

(deftest map-merge-test
  (testing "merge"
    (is (= {:a 1 :b 2} (merge {:a 1} {:b 2})))
    (is (= {:a 2} (merge {:a 1} {:a 2}))) ; later wins
    (is (= {:a 1 :b 2 :c 3} (merge {:a 1} {:b 2} {:c 3})))))

(deftest map-merge-with-test
  (testing "merge-with"
    (is (= {:a 3} (merge-with + {:a 1} {:a 2})))
    (is (= {:a 6 :b 2} (merge-with + {:a 1 :b 2} {:a 5})))))

(deftest map-select-keys-test
  (testing "select-keys"
    (is (= {:a 1} (select-keys {:a 1 :b 2 :c 3} [:a])))
    (is (= {:a 1 :c 3} (select-keys {:a 1 :b 2 :c 3} [:a :c])))
    (is (= {} (select-keys {:a 1} [:b])))))

(deftest map-update-test
  (testing "update"
    (is (= {:a 2} (update {:a 1} :a inc)))
    (is (= {:a 10} (update {:a 1} :a + 9)))
    (is (= {:a 1} (update {:a nil} :a (fnil inc 0))))))

(deftest map-assoc-in-test
  (testing "assoc-in"
    (is (= {:a {:b 1}} (assoc-in {} [:a :b] 1)))
    (is (= {:a {:b 2}} (assoc-in {:a {:b 1}} [:a :b] 2)))
    (is (= {:a {:b {:c 3}}} (assoc-in {} [:a :b :c] 3)))))

(deftest map-get-in-test
  (testing "get-in"
    (is (= 1 (get-in {:a {:b 1}} [:a :b])))
    (is (nil? (get-in {:a {:b 1}} [:a :c])))
    (is (= :default (get-in {:a 1} [:a :b] :default)))))

(deftest map-update-in-test
  (testing "update-in"
    (is (= {:a {:b 2}} (update-in {:a {:b 1}} [:a :b] inc)))
    (is (= {:a {:b 10}} (update-in {:a {:b 1}} [:a :b] + 9)))))

;; =============================================================================
;; Sets
;; =============================================================================

(deftest set-creation-test
  (testing "hash-set function"
    (is (= #{} (hash-set)))
    (is (= #{1} (hash-set 1)))
    (is (= #{1 2 3} (hash-set 1 2 3))))
  (testing "set function"
    (is (= #{1 2 3} (set [1 2 3])))
    (is (= #{1 2 3} (set '(1 2 3))))
    (is (= #{} (set nil)))))

(deftest set-predicate-test
  (testing "set?"
    (is (true? (set? #{})))
    (is (true? (set? #{1 2})))
    (is (false? (set? [])))
    (is (false? (set? nil)))))

(deftest set-count-test
  (testing "count on set"
    (is (= 0 (count #{})))
    (is (= 1 (count #{1})))
    (is (= 3 (count #{1 2 3})))))

(deftest set-contains-test
  (testing "contains? on set"
    (is (true? (contains? #{1 2 3} 1)))
    (is (true? (contains? #{1 2 3} 2)))
    (is (false? (contains? #{1 2 3} 4)))))

(deftest set-as-function-test
  (testing "set as function (membership)"
    (is (= 1 (#{1 2 3} 1)))
    (is (= 2 (#{1 2 3} 2)))
    (is (nil? (#{1 2 3} 4)))))

(deftest set-conj-test
  (testing "conj on set"
    (is (= #{1 2 3} (conj #{1 2} 3)))
    (is (= #{1 2} (conj #{1 2} 2))) ; no duplicate
    (is (= #{1 2 3 4} (conj #{1 2} 3 4)))))

(deftest set-disj-test
  (testing "disj on set"
    (is (= #{2 3} (disj #{1 2 3} 1)))
    (is (= #{1 2 3} (disj #{1 2 3} 4))) ; not present
    (is (= #{3} (disj #{1 2 3} 1 2)))))

(deftest set-union-test
  (testing "clojure.set/union"
    (is (= #{1 2 3 4} (clojure.set/union #{1 2} #{3 4})))
    (is (= #{1 2 3} (clojure.set/union #{1 2} #{2 3})))))

(deftest set-intersection-test
  (testing "clojure.set/intersection"
    (is (= #{2} (clojure.set/intersection #{1 2} #{2 3})))
    (is (= #{} (clojure.set/intersection #{1 2} #{3 4})))))

(deftest set-difference-test
  (testing "clojure.set/difference"
    (is (= #{1} (clojure.set/difference #{1 2} #{2 3})))
    (is (= #{1 2} (clojure.set/difference #{1 2} #{3 4})))))

(deftest set-subset-superset-test
  (testing "clojure.set/subset?"
    (is (true? (clojure.set/subset? #{1} #{1 2})))
    (is (true? (clojure.set/subset? #{} #{1 2})))
    (is (false? (clojure.set/subset? #{1 2} #{1}))))
  (testing "clojure.set/superset?"
    (is (true? (clojure.set/superset? #{1 2} #{1})))
    (is (false? (clojure.set/superset? #{1} #{1 2})))))

;; =============================================================================
;; General Collection Functions
;; =============================================================================

(deftest empty-test
  (testing "empty?"
    (is (true? (empty? [])))
    (is (true? (empty? '())))
    (is (true? (empty? {})))
    (is (true? (empty? #{})))
    (is (true? (empty? nil)))
    (is (false? (empty? [1])))
    (is (false? (empty? {:a 1})))))

(deftest empty-coll-test
  (testing "empty returns empty collection of same type"
    (is (= [] (empty [1 2 3])))
    (is (= '() (empty '(1 2 3))))
    (is (= {} (empty {:a 1})))
    (is (= #{} (empty #{1 2})))))

(deftest into-test
  (testing "into"
    (is (= [1 2 3] (into [] '(1 2 3))))
    (is (= {:a 1 :b 2} (into {} [[:a 1] [:b 2]])))
    (is (= #{1 2 3} (into #{} [1 2 3 2 1])))
    (is (= [1 2 3 4] (into [1 2] [3 4])))))

(deftest into-with-transducer-test
  (testing "into with transducer"
    (is (= [2 4 6] (into [] (map #(* % 2)) [1 2 3])))
    (is (= [2 4] (into [] (filter even?) [1 2 3 4])))))

(deftest coll-test
  (testing "coll?"
    (is (true? (coll? [])))
    (is (true? (coll? '())))
    (is (true? (coll? {})))
    (is (true? (coll? #{})))
    (is (false? (coll? nil)))
    (is (false? (coll? 1)))
    (is (false? (coll? "string")))))

(deftest sequential-test
  (testing "sequential?"
    (is (true? (sequential? [])))
    (is (true? (sequential? '())))
    (is (false? (sequential? {})))
    (is (false? (sequential? #{})))
    (is (false? (sequential? nil)))))

(deftest associative-test
  (testing "associative?"
    (is (true? (associative? [])))
    (is (true? (associative? {})))
    (is (false? (associative? '())))
    (is (false? (associative? #{})))))

(deftest counted-test
  (testing "counted?"
    (is (true? (counted? [])))
    (is (true? (counted? {})))
    (is (true? (counted? #{})))
    ;; Lazy seqs may not be counted
    (is (false? (counted? (map inc [1 2 3]))))))

;; =============================================================================
;; Negative Index Edge Cases (nth/assoc)
;; =============================================================================

(deftest nth-negative-index-test
  (testing "nth with negative index"
    ;; In Clojure, negative indexes throw IndexOutOfBoundsException
    (is (thrown? Exception (nth [1 2 3] -1)))
    (is (thrown? Exception (nth [1 2 3] -5)))
    (is (thrown? Exception (nth '(1 2 3) -1))))
  (testing "nth with negative index and default"
    ;; With default value, should still throw (doesn't use default)
    (is (thrown? Exception (nth [1 2 3] -1 :default)))))

(deftest assoc-negative-index-test
  (testing "assoc on vector with negative index"
    ;; In Clojure, negative indexes throw IndexOutOfBoundsException
    (is (thrown? Exception (assoc [1 2 3] -1 :x)))
    (is (thrown? Exception (assoc [1 2 3] -5 :x)))
    (is (thrown? Exception (assoc [] -1 :x)))))

(deftest get-negative-index-test
  (testing "get on vector with negative index"
    ;; get returns nil for negative indexes (doesn't throw)
    (is (nil? (get [1 2 3] -1)))
    (is (nil? (get [1 2 3] -5))))
  (testing "get with negative index and default"
    ;; Returns default for negative indexes
    (is (= :default (get [1 2 3] -1 :default)))))

(run-all-tests)
