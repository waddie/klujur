;; collections_test.cljc - Tests for Klujur collection operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.collections-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Lists
;; =============================================================================

(deftest list-creation-test
  (testing "list function"
    (is (= '() (eval* "(list)")))
    (is (= '(1) (eval* "(list 1)")))
    (is (= '(1 2 3) (eval* "(list 1 2 3)"))))
  (testing "list evaluates arguments"
    (is (= '(2 4 6) (eval* "(list (+ 1 1) (+ 2 2) (+ 3 3))")))))

(deftest list-predicate-test
  (testing "list?"
    (is (true? (eval* "(list? '())")))
    (is (true? (eval* "(list? '(1 2 3))")))
    (is (true? (eval* "(list? (list 1 2))")))
    (is (false? (eval* "(list? [])")))
    (is (false? (eval* "(list? nil)")))))

(deftest list-count-test
  (testing "count on list"
    (is (= 0 (eval* "(count '())")))
    (is (= 1 (eval* "(count '(1))")))
    (is (= 3 (eval* "(count '(1 2 3))")))))

(deftest list-nth-test
  (testing "nth on list"
    (is (= 1 (eval* "(nth '(1 2 3) 0)")))
    (is (= 2 (eval* "(nth '(1 2 3) 1)")))
    (is (= 3 (eval* "(nth '(1 2 3) 2)"))))
  (testing "nth with not-found"
    (is (= :default (eval* "(nth '(1 2) 5 :default)"))))
  (testing "nth out of bounds"
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(nth '(1 2) 5)")))))

(deftest list-peek-pop-test
  (testing "peek on list (returns first)"
    (is (= 1 (eval* "(peek '(1 2 3))")))
    (is (nil? (eval* "(peek '())"))))
  (testing "pop on list (removes first)"
    (is (= '(2 3) (eval* "(pop '(1 2 3))")))
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(pop '())")))))

(deftest list-conj-test
  (testing "conj on list (adds to front)"
    (is (= '(0 1 2 3) (eval* "(conj '(1 2 3) 0)")))
    (is (= '(1) (eval* "(conj '() 1)")))
    (is (= '(-1 0 1 2 3) (eval* "(conj '(1 2 3) 0 -1)")))))

;; =============================================================================
;; Vectors
;; =============================================================================

(deftest vector-creation-test
  (testing "vector function"
    (is (= [] (eval* "(vector)")))
    (is (= [1] (eval* "(vector 1)")))
    (is (= [1 2 3] (eval* "(vector 1 2 3)"))))
  (testing "vec function"
    (is (= [1 2 3] (eval* "(vec '(1 2 3))")))
    (is (= [1 2 3] (eval* "(vec [1 2 3])")))
    (is (= [] (eval* "(vec nil)")))))

(deftest vector-predicate-test
  (testing "vector?"
    (is (true? (eval* "(vector? [])")))
    (is (true? (eval* "(vector? [1 2 3])")))
    (is (false? (eval* "(vector? '(1 2 3))")))
    (is (false? (eval* "(vector? nil)")))))

(deftest vector-count-test
  (testing "count on vector"
    (is (= 0 (eval* "(count [])")))
    (is (= 1 (eval* "(count [1])")))
    (is (= 3 (eval* "(count [1 2 3])")))))

(deftest vector-nth-test
  (testing "nth on vector"
    (is (= 1 (eval* "(nth [1 2 3] 0)")))
    (is (= 2 (eval* "(nth [1 2 3] 1)")))
    (is (= 3 (eval* "(nth [1 2 3] 2)"))))
  (testing "nth with not-found"
    (is (= :default (eval* "(nth [1 2] 5 :default)"))))
  (testing "nth out of bounds"
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(nth [1 2] 5)")))))

(deftest vector-get-test
  (testing "get on vector"
    (is (= 1 (eval* "(get [1 2 3] 0)")))
    (is (= 2 (eval* "(get [1 2 3] 1)")))
    (is (nil? (eval* "(get [1 2 3] 5)"))))
  (testing "get with not-found"
    (is (= :default (eval* "(get [1 2] 5 :default)")))))

(deftest vector-peek-pop-test
  (testing "peek on vector (returns last)"
    (is (= 3 (eval* "(peek [1 2 3])")))
    (is (nil? (eval* "(peek [])"))))
  (testing "pop on vector (removes last)"
    (is (= [1 2] (eval* "(pop [1 2 3])")))
    (is (thrown? #?(:clj Exception
                    :cljs js/Error)
                 (eval* "(pop [])")))))

(deftest vector-conj-test
  (testing "conj on vector (adds to end)"
    (is (= [1 2 3 4] (eval* "(conj [1 2 3] 4)")))
    (is (= [1] (eval* "(conj [] 1)")))
    (is (= [1 2 3 4 5] (eval* "(conj [1 2 3] 4 5)")))))

(deftest vector-assoc-test
  (testing "assoc on vector"
    (is (= [1 :x 3] (eval* "(assoc [1 2 3] 1 :x)")))
    (is (= [:a 2 3] (eval* "(assoc [1 2 3] 0 :a)")))
    (is (= [1 2 :c] (eval* "(assoc [1 2 3] 2 :c)")))))

(deftest vector-subvec-test
  (testing "subvec"
    (is (= [2 3] (eval* "(subvec [1 2 3 4] 1 3)")))
    (is (= [2 3 4] (eval* "(subvec [1 2 3 4] 1)")))
    (is (= [] (eval* "(subvec [1 2 3] 2 2)")))))

(deftest vector-as-function-test
  (testing "vector as function (lookup)"
    (is (= :b (eval* "([:a :b :c] 1)")))
    (is (nil? (eval* "([:a :b] 5)")))))

;; =============================================================================
;; Maps
;; =============================================================================

(deftest map-creation-test
  (testing "hash-map function"
    (is (= {} (eval* "(hash-map)")))
    (is (= {:a 1} (eval* "(hash-map :a 1)")))
    (is (= {:a 1 :b 2} (eval* "(hash-map :a 1 :b 2)"))))
  (testing "array-map function"
    (is (= {} (eval* "(array-map)")))
    (is (= {:a 1 :b 2} (eval* "(array-map :a 1 :b 2)")))))

(deftest map-predicate-test
  (testing "map?"
    (is (true? (eval* "(map? {})")))
    (is (true? (eval* "(map? {:a 1})")))
    (is (false? (eval* "(map? [])")))
    (is (false? (eval* "(map? nil)")))))

(deftest map-count-test
  (testing "count on map"
    (is (= 0 (eval* "(count {})")))
    (is (= 1 (eval* "(count {:a 1})")))
    (is (= 2 (eval* "(count {:a 1 :b 2})")))))

(deftest map-get-test
  (testing "get on map"
    (is (= 1 (eval* "(get {:a 1 :b 2} :a)")))
    (is (= 2 (eval* "(get {:a 1 :b 2} :b)")))
    (is (nil? (eval* "(get {:a 1} :c)"))))
  (testing "get with not-found"
    (is (= :default (eval* "(get {:a 1} :c :default)")))))

(deftest map-as-function-test
  (testing "map as function (lookup)"
    (is (= 1 (eval* "({:a 1 :b 2} :a)")))
    (is (= 2 (eval* "({:a 1 :b 2} :b)")))
    (is (nil? (eval* "({:a 1} :c)")))
    (is (= :default (eval* "({:a 1} :c :default)")))))

(deftest keyword-as-function-test
  (testing "keyword as function (lookup)"
    (is (= 1 (eval* "(:a {:a 1 :b 2})")))
    (is (= 2 (eval* "(:b {:a 1 :b 2})")))
    (is (nil? (eval* "(:c {:a 1})")))
    (is (= :default (eval* "(:c {:a 1} :default)")))))

(deftest map-assoc-test
  (testing "assoc on map"
    (is (= {:a 1 :b 2} (eval* "(assoc {:a 1} :b 2)")))
    (is (= {:a 10} (eval* "(assoc {:a 1} :a 10)"))) ; replace
    (is (= {:a 1 :b 2 :c 3} (eval* "(assoc {:a 1} :b 2 :c 3)")))))

(deftest map-dissoc-test
  (testing "dissoc on map"
    (is (= {:b 2} (eval* "(dissoc {:a 1 :b 2} :a)")))
    (is (= {} (eval* "(dissoc {:a 1} :a)")))
    (is (= {:a 1} (eval* "(dissoc {:a 1} :b)"))) ; key not present
    (is (= {} (eval* "(dissoc {:a 1 :b 2} :a :b)")))))

(deftest map-keys-vals-test
  (testing "keys"
    (is (= #{:a :b} (set (eval* "(keys {:a 1 :b 2})"))))
    (is (nil? (eval* "(keys {})"))))
  (testing "vals"
    (is (= #{1 2} (set (eval* "(vals {:a 1 :b 2})"))))
    (is (nil? (eval* "(vals {})")))))

(deftest map-contains-test
  (testing "contains?"
    (is (true? (eval* "(contains? {:a 1} :a)")))
    (is (false? (eval* "(contains? {:a 1} :b)")))
    (is (true? (eval* "(contains? {:a nil} :a)")))) ; nil value, key exists
  (testing "contains? on vector (index check)"
    (is (true? (eval* "(contains? [1 2 3] 0)")))
    (is (true? (eval* "(contains? [1 2 3] 2)")))
    (is (false? (eval* "(contains? [1 2 3] 3)")))))

(deftest map-merge-test
  (testing "merge"
    (is (= {:a 1 :b 2} (eval* "(merge {:a 1} {:b 2})")))
    (is (= {:a 2} (eval* "(merge {:a 1} {:a 2})"))) ; later wins
    (is (= {:a 1 :b 2 :c 3} (eval* "(merge {:a 1} {:b 2} {:c 3})")))))

(deftest map-merge-with-test
  (testing "merge-with"
    (is (= {:a 3} (eval* "(merge-with + {:a 1} {:a 2})")))
    (is (= {:a 6 :b 2} (eval* "(merge-with + {:a 1 :b 2} {:a 5})")))))

(deftest map-select-keys-test
  (testing "select-keys"
    (is (= {:a 1} (eval* "(select-keys {:a 1 :b 2 :c 3} [:a])")))
    (is (= {:a 1 :c 3} (eval* "(select-keys {:a 1 :b 2 :c 3} [:a :c])")))
    (is (= {} (eval* "(select-keys {:a 1} [:b])")))))

(deftest map-update-test
  (testing "update"
    (is (= {:a 2} (eval* "(update {:a 1} :a inc)")))
    (is (= {:a 10} (eval* "(update {:a 1} :a + 9)")))
    (is (= {:a 1} (eval* "(update {:a nil} :a (fnil inc 0))")))))

(deftest map-assoc-in-test
  (testing "assoc-in"
    (is (= {:a {:b 1}} (eval* "(assoc-in {} [:a :b] 1)")))
    (is (= {:a {:b 2}} (eval* "(assoc-in {:a {:b 1}} [:a :b] 2)")))
    (is (= {:a {:b {:c 3}}} (eval* "(assoc-in {} [:a :b :c] 3)")))))

(deftest map-get-in-test
  (testing "get-in"
    (is (= 1 (eval* "(get-in {:a {:b 1}} [:a :b])")))
    (is (nil? (eval* "(get-in {:a {:b 1}} [:a :c])")))
    (is (= :default (eval* "(get-in {:a 1} [:a :b] :default)")))))

(deftest map-update-in-test
  (testing "update-in"
    (is (= {:a {:b 2}} (eval* "(update-in {:a {:b 1}} [:a :b] inc)")))
    (is (= {:a {:b 10}} (eval* "(update-in {:a {:b 1}} [:a :b] + 9)")))))

;; =============================================================================
;; Sets
;; =============================================================================

(deftest set-creation-test
  (testing "hash-set function"
    (is (= #{} (eval* "(hash-set)")))
    (is (= #{1} (eval* "(hash-set 1)")))
    (is (= #{1 2 3} (eval* "(hash-set 1 2 3)"))))
  (testing "set function"
    (is (= #{1 2 3} (eval* "(set [1 2 3])")))
    (is (= #{1 2 3} (eval* "(set '(1 2 3))")))
    (is (= #{} (eval* "(set nil)")))))

(deftest set-predicate-test
  (testing "set?"
    (is (true? (eval* "(set? #{})")))
    (is (true? (eval* "(set? #{1 2})")))
    (is (false? (eval* "(set? [])")))
    (is (false? (eval* "(set? nil)")))))

(deftest set-count-test
  (testing "count on set"
    (is (= 0 (eval* "(count #{})")))
    (is (= 1 (eval* "(count #{1})")))
    (is (= 3 (eval* "(count #{1 2 3})")))))

(deftest set-contains-test
  (testing "contains? on set"
    (is (true? (eval* "(contains? #{1 2 3} 1)")))
    (is (true? (eval* "(contains? #{1 2 3} 2)")))
    (is (false? (eval* "(contains? #{1 2 3} 4)")))))

(deftest set-as-function-test
  (testing "set as function (membership)"
    (is (= 1 (eval* "(#{1 2 3} 1)")))
    (is (= 2 (eval* "(#{1 2 3} 2)")))
    (is (nil? (eval* "(#{1 2 3} 4)")))))

(deftest set-conj-test
  (testing "conj on set"
    (is (= #{1 2 3} (eval* "(conj #{1 2} 3)")))
    (is (= #{1 2} (eval* "(conj #{1 2} 2)"))) ; no duplicate
    (is (= #{1 2 3 4} (eval* "(conj #{1 2} 3 4)")))))

(deftest set-disj-test
  (testing "disj on set"
    (is (= #{2 3} (eval* "(disj #{1 2 3} 1)")))
    (is (= #{1 2 3} (eval* "(disj #{1 2 3} 4)"))) ; not present
    (is (= #{3} (eval* "(disj #{1 2 3} 1 2)")))))

(deftest set-union-test
  (testing "clojure.set/union"
    (is (= #{1 2 3 4} (eval* "(clojure.set/union #{1 2} #{3 4})")))
    (is (= #{1 2 3} (eval* "(clojure.set/union #{1 2} #{2 3})")))))

(deftest set-intersection-test
  (testing "clojure.set/intersection"
    (is (= #{2} (eval* "(clojure.set/intersection #{1 2} #{2 3})")))
    (is (= #{} (eval* "(clojure.set/intersection #{1 2} #{3 4})")))))

(deftest set-difference-test
  (testing "clojure.set/difference"
    (is (= #{1} (eval* "(clojure.set/difference #{1 2} #{2 3})")))
    (is (= #{1 2} (eval* "(clojure.set/difference #{1 2} #{3 4})")))))

(deftest set-subset-superset-test
  (testing "clojure.set/subset?"
    (is (true? (eval* "(clojure.set/subset? #{1} #{1 2})")))
    (is (true? (eval* "(clojure.set/subset? #{} #{1 2})")))
    (is (false? (eval* "(clojure.set/subset? #{1 2} #{1})"))))
  (testing "clojure.set/superset?"
    (is (true? (eval* "(clojure.set/superset? #{1 2} #{1})")))
    (is (false? (eval* "(clojure.set/superset? #{1} #{1 2})")))))

;; =============================================================================
;; General Collection Functions
;; =============================================================================

(deftest empty-test
  (testing "empty?"
    (is (true? (eval* "(empty? [])")))
    (is (true? (eval* "(empty? '())")))
    (is (true? (eval* "(empty? {})")))
    (is (true? (eval* "(empty? #{})")))
    (is (true? (eval* "(empty? nil)")))
    (is (false? (eval* "(empty? [1])")))
    (is (false? (eval* "(empty? {:a 1})")))))

(deftest empty-coll-test
  (testing "empty returns empty collection of same type"
    (is (= [] (eval* "(empty [1 2 3])")))
    (is (= '() (eval* "(empty '(1 2 3))")))
    (is (= {} (eval* "(empty {:a 1})")))
    (is (= #{} (eval* "(empty #{1 2})")))))

(deftest into-test
  (testing "into"
    (is (= [1 2 3] (eval* "(into [] '(1 2 3))")))
    (is (= {:a 1 :b 2} (eval* "(into {} [[:a 1] [:b 2]])")))
    (is (= #{1 2 3} (eval* "(into #{} [1 2 3 2 1])")))
    (is (= [1 2 3 4] (eval* "(into [1 2] [3 4])")))))

(deftest into-with-transducer-test
  (testing "into with transducer"
    (is (= [2 4 6] (eval* "(into [] (map #(* % 2)) [1 2 3])")))
    (is (= [2 4] (eval* "(into [] (filter even?) [1 2 3 4])")))))

(deftest coll-test
  (testing "coll?"
    (is (true? (eval* "(coll? [])")))
    (is (true? (eval* "(coll? '())")))
    (is (true? (eval* "(coll? {})")))
    (is (true? (eval* "(coll? #{})")))
    (is (false? (eval* "(coll? nil)")))
    (is (false? (eval* "(coll? 1)")))
    (is (false? (eval* "(coll? \"string\")")))))

(deftest sequential-test
  (testing "sequential?"
    (is (true? (eval* "(sequential? [])")))
    (is (true? (eval* "(sequential? '())")))
    (is (false? (eval* "(sequential? {})")))
    (is (false? (eval* "(sequential? #{})")))
    (is (false? (eval* "(sequential? nil)")))))

(deftest associative-test
  (testing "associative?"
    (is (true? (eval* "(associative? [])")))
    (is (true? (eval* "(associative? {})")))
    (is (false? (eval* "(associative? '())")))
    (is (false? (eval* "(associative? #{})")))))

(deftest counted-test
  (testing "counted?"
    (is (true? (eval* "(counted? [])")))
    (is (true? (eval* "(counted? {})")))
    (is (true? (eval* "(counted? #{})")))
    ;; Lazy seqs may not be counted
    (is (false? (eval* "(counted? (map inc [1 2 3]))")))))
