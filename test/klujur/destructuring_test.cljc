;; destructuring_test.cljc - Tests for Klujur destructuring
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.destructuring-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Sequential Destructuring (Vectors/Lists)
;; =============================================================================

(deftest sequential-basic-test
  (testing "basic sequential destructuring"
    (is (= 1
           (let [[a] [1 2 3]]
             a)))
    (is (= [1 2]
           (let [[a b] [1 2 3]]
             [a b])))
    (is (= [1 2 3]
           (let [[a b c] [1 2 3]]
             [a b c])))))

(deftest sequential-with-list-test
  (testing "destructuring from list"
    (is (= 1
           (let [[a] '(1 2 3)]
             a)))
    (is (= [1 2]
           (let [[a b] '(1 2 3)]
             [a b])))))

(deftest sequential-fewer-elements-test
  (testing "fewer elements than bindings"
    (is (= [1 nil]
           (let [[a b] [1]]
             [a b])))
    (is (= [1 nil nil]
           (let [[a b c] [1]]
             [a b c])))))

(deftest sequential-rest-test
  (testing "& rest in sequential destructuring"
    (is (= [1 '(2 3)]
           (let [[a & rest] [1 2 3]]
             [a rest])))
    (is (= [1 nil]
           (let [[a & rest] [1]]
             [a rest])))
    (is (= [1 2 '(3 4 5)]
           (let [[a b & rest] [1 2 3 4 5]]
             [a b rest])))))

(deftest sequential-as-test
  (testing ":as in sequential destructuring"
    (is (= [[1 2 3] 1]
           (let [[a :as all] [1 2 3]]
             [all a])))
    (is (= [[1 2 3] 1 2]
           (let [[a b :as all] [1 2 3]]
             [all a b])))
    (is (= [[1 2 3] 1 '(2 3)]
           (let [[a & rest :as all] [1 2 3]]
             [all a rest])))))

(deftest sequential-nested-test
  (testing "nested sequential destructuring"
    (is (= [1 2]
           (let [[[a b]] [[1 2]]]
             [a b])))
    (is (= [1 2 3 4]
           (let [[[a b] [c d]] [[1 2] [3 4]]]
             [a b c d])))
    (is (= [1 3]
           (let [[a [b]] [1 [3]]]
             [a b])))))

(deftest sequential-in-fn-test
  (testing "sequential destructuring in fn params"
    (is (= [1 2] ((fn [[a b]] [a b]) [1 2])))
    (is (= [1 '(2 3)] ((fn [[a & rest]] [a rest]) [1 2 3])))))

;; =============================================================================
;; Map Destructuring
;; =============================================================================

(deftest map-basic-test
  (testing "basic map destructuring with :keys"
    (is (= 1
           (let [{:keys [a]} {:a 1}]
             a)))
    (is (= [1 2]
           (let [{:keys [a b]} {:a 1 :b 2}]
             [a b])))
    (is (= [1 2 3]
           (let [{:keys [a b c]} {:a 1 :b 2 :c 3}]
             [a b c])))))

(deftest map-missing-keys-test
  (testing "missing keys bind to nil"
    (is (= [1 nil]
           (let [{:keys [a b]} {:a 1}]
             [a b])))
    (is (= [nil nil]
           (let [{:keys [a b]} {}]
             [a b])))))

(deftest map-keys-keyword-syntax-test
  (testing ":keys with keyword syntax"
    ;; :keys [:a :b] is equivalent to :keys [a b]
    (is (= [1 2]
           (let [{:keys [:a :b]} {:a 1 :b 2}]
             [a b])))))

(deftest map-strs-test
  (testing ":strs for string keys"
    (is (= 1
           (let [{:strs [a]} {"a" 1}]
             a)))
    (is (= [1 2]
           (let [{:strs [a b]} {"a" 1 "b" 2}]
             [a b])))))

(deftest map-syms-test
  (testing ":syms for symbol keys"
    (is (= 1
           (let [{:syms [a]} {'a 1}]
             a)))
    (is (= [1 2]
           (let [{:syms [a b]} {'a 1 'b 2}]
             [a b])))))

(deftest map-explicit-keys-test
  (testing "explicit key bindings"
    (is (= 1
           (let [{x :a} {:a 1}]
             x)))
    (is (= [1 2]
           (let [{x :a y :b} {:a 1 :b 2}]
             [x y])))
    (is (= 1
           (let [{x "a"} {"a" 1}]
             x)))))

(deftest map-or-defaults-test
  (testing ":or for defaults"
    (is (= 1
           (let [{:keys [a] :or {a 1}} {}]
             a)))
    (is (= [1 :default]
           (let [{:keys [a b] :or {b :default}} {:a 1}]
             [a b])))
    (is (= [1 10]
           (let [{:keys [a b] :or {b 2}} {:a 1 :b 10}]
             [a b])))) ; :or not used when key present
  (testing ":or with false value"
    ;; false is a valid value, :or should not override it
    (is (= false
           (let [{:keys [a] :or {a true}} {:a false}]
             a)))))

(deftest map-as-test
  (testing ":as in map destructuring"
    (is (= [{:a 1 :b 2} 1 2]
           (let [{:keys [a b] :as m} {:a 1 :b 2}]
             [m a b])))
    (is (= {:a 1}
           (let [{:as m} {:a 1}]
             m)))))

(deftest map-nested-test
  (testing "nested map destructuring"
    (is (= 1
           (let [{{:keys [a]} :inner} {:inner {:a 1}}]
             a)))
    (is (= [1 2]
           (let [{{:keys [a b]} :inner} {:inner {:a 1 :b 2}}]
             [a b])))))

(deftest map-combined-test
  (testing "combining :keys, :or, :as"
    (is (= [{:a 1} 1 :default]
           (let [{:keys [a b] :or {b :default} :as m} {:a 1}]
             [m a b])))))

;; =============================================================================
;; Namespaced Keys Destructuring
;; =============================================================================

(deftest namespaced-keys-test
  (testing ":keys with namespaced keywords"
    (is (= 1
           (let [{:keys [a/b]} {:a/b 1}]
             b)))
    (is (= [1 2]
           (let [{:keys [a/x b/y]} {:a/x 1 :b/y 2}]
             [x y])))))

(deftest ns-keys-shorthand-test
  (testing "namespace shorthand :ns/keys"
    (is (= [1 2]
           (let [{:user/keys [name age]} {:user/name 1 :user/age 2}]
             [name age])))
    (is (= [1 2 3]
           (let [{:person/keys [a b c]} {:person/a 1 :person/b 2 :person/c 3}]
             [a b c])))))

(deftest ns-syms-shorthand-test
  (testing "namespace shorthand :ns/syms"
    (is (= [1 2]
           (let [{:user/syms [name age]} {'user/name 1 'user/age 2}]
             [name age])))))

;; =============================================================================
;; Mixed Sequential and Map Destructuring
;; =============================================================================

(deftest mixed-destructuring-test
  (testing "map inside sequential"
    (is (= [1 2 3]
           (let [[{:keys [a b]} c] [{:a 1 :b 2} 3]]
             [a b c]))))
  (testing "sequential inside map"
    (is (= [1 2 3]
           (let [{[a b] :vec c :c} {:vec [1 2] :c 3}]
             [a b c])))))

(deftest deeply-nested-test
  (testing "deeply nested destructuring"
    (is (= 1
           (let [{{[a] :inner} :outer} {:outer {:inner [1]}}]
             a)))
    (is (= [1 2 3]
           (let [[{:keys [a]} {:keys [b]} c] [{:a 1} {:b 2} 3]]
             [a b c])))))

;; =============================================================================
;; Destructuring in defn
;; =============================================================================

(deftest defn-sequential-destructure-test
  (testing "defn with sequential destructuring"
    (is (= 3 (do (defn add-pair [[a b]] (+ a b)) (add-pair [1 2]))))
    (is (= [1 '(2 3)]
           (do (defn split-first [[a & rest]] [a rest])
               (split-first [1 2 3]))))))

(deftest defn-map-destructure-test
  (testing "defn with map destructuring"
    (is (= "Hello, World"
           (do (defn greet [{:keys [name]}] (str "Hello, " name))
               (greet {:name "World"}))))
    (is (= "Hello, Guest"
           (do (defn greet-default
                 [{:keys [name] :or {name "Guest"}}]
                 (str "Hello, " name))
               (greet-default {}))))))

(deftest defn-multi-arity-destructure-test
  (testing "defn multi-arity with destructuring"
    (is (= [1 2]
           (do
             (defn f ([{:keys [a]}] [a nil]) ([{:keys [a]} {:keys [b]}] [a b]))
             (f {:a 1} {:b 2}))))))

;; =============================================================================
;; Destructuring in loop
;; =============================================================================

(deftest loop-sequential-destructure-test
  (testing "loop with sequential destructuring"
    (is (= 6
           (loop [[a & rest] [1 2 3]
                  sum        0]
             (if a (recur rest (+ sum a)) sum))))))

(deftest loop-map-destructure-test
  (testing "loop with map destructuring"
    (is (= [:a 1]
           (loop [{:keys [a b] :as m} {:a 1 :b 2}]
             [a b])))))

;; =============================================================================
;; Destructuring in for
;; =============================================================================

(deftest for-destructure-test
  (testing "for with sequential destructuring"
    (is (= '(3 7)
           (for [[a b] [[1 2] [3 4]]]
             (+ a b)))))
  (testing "for with map destructuring"
    (is (= '(1 2)
           (for [{:keys [x]} [{:x 1} {:x 2}]]
             x)))))

;; =============================================================================
;; Destructuring Edge Cases
;; =============================================================================

(deftest empty-destructuring-test
  (testing "empty sequential destructure"
    (is (= nil
           (let [[] [1 2 3]]
             nil))))
  (testing "empty map destructure"
    (is (= nil
           (let [{} {:a 1}]
             nil)))))

(deftest destructure-nil-test
  (testing "destructuring nil"
    (is (= [nil nil]
           (let [[a b] nil]
             [a b])))
    (is (= [nil nil]
           (let [{:keys [a b]} nil]
             [a b])))
    (is (= [:default nil]
           (let [{:keys [a b] :or {a :default}} nil]
             [a b])))))

(deftest or-doesnt-create-bindings-test
  (testing ":or does not create bindings"
    ;; :or {c 3} should NOT create binding 'c' if not in :keys
    (is (thrown? Exception
                 (let [{:keys [a b] :or {c 3}} {:a 1}]
                   c)))))

(deftest keywords-not-allowed-as-bindings-test
  (testing "keywords cannot be used as binding names"
    (is (thrown? Exception
                 (let [:a 1]
                   :a)))))

;; =============================================================================
;; Destructuring with :as Preserves Original
;; =============================================================================

(deftest as-preserves-original-test
  (testing ":as gives original, not transformed"
    ;; When destructuring from a vector, :as gives the vector, not a seq
    (is (vector? (let [[a :as all] [1 2 3]]
                   all)))
    ;; When destructuring from a map, :as gives the map
    (is (map? (let [{:keys [a] :as m} {:a 1}]
                m)))))

;; =============================================================================
;; Argument Destructuring Edge Cases
;; =============================================================================

(deftest fn-destructure-with-rest-test
  (testing "fn destructuring with rest args"
    (is (= [[1 2] [3 4 5]] ((fn [[a b] & rest] [[a b] rest]) [1 2] 3 4 5)))
    (is (= [{:a 1} '({:b 2} {:c 3})]
           ((fn [{:keys [a] :as first} & rest] [first rest])
            {:a 1}
            {:b 2}
            {:c 3})))))

(deftest multiple-rest-args-error-test
  (testing "multiple & rest args should error"
    (is (thrown? Exception
                 (let [[a & b & c] [1 2 3]]
                   a)))))

(run-all-tests)
