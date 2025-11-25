;; logic_test.cljc - Tests for Klujur logic and truthiness
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.logic-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; Helper function for short-circuit testing
(defn exception
  []
  (throw (ex-info "Should not be reached - short-circuit evaluation failed"
                  {})))

;; =============================================================================
;; Truthiness Fundamentals
;; =============================================================================
;; In Clojure, only nil and false are falsy. Everything else is truthy.

(deftest falsy-values-test
  (testing "nil is falsy"
    (is (= :falsy (if nil :truthy :falsy)))
    (is (false? (boolean nil))))
  (testing "false is falsy"
    (is (= :falsy (if false :truthy :falsy)))
    (is (false? (boolean false)))))

(deftest truthy-values-test
  (testing "true is truthy"
    (is (= :truthy (if true :truthy :falsy)))
    (is (true? (boolean true))))
  (testing "numbers are truthy (including zero)"
    (is (= :truthy (if 0 :truthy :falsy)))
    (is (= :truthy (if 1 :truthy :falsy)))
    (is (= :truthy (if -1 :truthy :falsy)))
    (is (= :truthy (if 0.0 :truthy :falsy)))
    (is (= :truthy (if 0.1 :truthy :falsy))))
  (testing "strings are truthy (including empty)"
    (is (= :truthy (if "" :truthy :falsy)))
    (is (= :truthy (if "hello" :truthy :falsy))))
  (testing "collections are truthy (including empty)"
    (is (= :truthy (if '() :truthy :falsy)))
    (is (= :truthy (if [] :truthy :falsy)))
    (is (= :truthy (if {} :truthy :falsy)))
    (is (= :truthy (if #{} :truthy :falsy)))
    (is (= :truthy (if [1 2 3] :truthy :falsy))))
  (testing "keywords and symbols are truthy"
    (is (= :truthy (if :keyword :truthy :falsy)))
    (is (= :truthy (if 'symbol :truthy :falsy)))))

;; =============================================================================
;; boolean
;; =============================================================================

(deftest boolean-coercion-test
  (testing "boolean coerces to true/false"
    (is (true? (boolean true)))
    (is (false? (boolean false)))
    (is (false? (boolean nil)))
    (is (true? (boolean 0)))
    (is (true? (boolean "")))
    (is (true? (boolean [])))
    (is (true? (boolean :keyword)))))

;; =============================================================================
;; not
;; =============================================================================

(deftest not-test
  (testing "not with truthy values"
    (is (false? (not true)))
    (is (false? (not 1)))
    (is (false? (not 0))) ; 0 is truthy!
    (is (false? (not ""))) ; empty string is truthy!
    (is (false? (not [])))  ; empty vector is truthy!
    (is (false? (not '()))) ; empty list is truthy!
    (is (false? (not {})))  ; empty map is truthy!
    (is (false? (not #{}))) ; empty set is truthy!
    (is (false? (not :keyword)))
    (is (false? (not 'symbol))))
  (testing "not with falsy values"
    (is (true? (not nil)))
    (is (true? (not false)))))

(deftest double-negation-test
  (testing "double negation"
    (is (false? (not (not nil))))
    (is (false? (not (not false))))
    (is (true? (not (not true))))
    (is (true? (not (not 0))))
    (is (true? (not (not []))))))

;; =============================================================================
;; and
;; =============================================================================

(deftest and-basic-test
  (testing "and with no arguments" (is (true? (and))))
  (testing "and with single argument"
    (is (= 1 (and 1)))
    (is (nil? (and nil)))
    (is (false? (and false))))
  (testing "and with multiple truthy arguments"
    (is (= 3 (and 1 2 3))) ; returns last
    (is (= :last (and :a :b :last)))))

(deftest and-short-circuit-test
  (testing "and short-circuits on false"
    (is (false? (and false (exception))))
    (is (false? (and true false (exception)))))
  (testing "and short-circuits on nil"
    (is (nil? (and nil (exception))))
    (is (nil? (and true nil (exception))))))

(deftest and-returns-first-falsy-test
  (testing "and returns first falsy value"
    (is (nil? (and nil false)))
    (is (false? (and false nil)))
    (is (nil? (and 1 2 nil 3)))
    (is (false? (and 1 false 2)))))

(deftest and-truthiness-test
  (testing "and respects Clojure truthiness"
    ;; 0 is truthy, so and continues
    (is (= :yes (and 0 :yes)))
    ;; empty string is truthy
    (is (= :yes (and "" :yes)))
    ;; empty collections are truthy
    (is (= :yes (and [] :yes)))
    (is (= :yes (and {} :yes)))
    (is (= :yes (and #{} :yes)))))

;; =============================================================================
;; or
;; =============================================================================

(deftest or-basic-test
  (testing "or with no arguments" (is (nil? (or))))
  (testing "or with single argument"
    (is (= 1 (or 1)))
    (is (nil? (or nil)))
    (is (false? (or false))))
  (testing "or with multiple falsy arguments"
    (is (nil? (or nil nil nil)))
    (is (false? (or false false)))
    (is (nil? (or nil false nil)))))  ; returns last evaluated

(deftest or-short-circuit-test
  (testing "or short-circuits on truthy value"
    (is (= 1 (or 1 (exception))))
    (is (= :first (or :first (exception))))
    (is (= 0 (or 0 (exception))))) ; 0 is truthy!
  (testing "or continues past falsy values"
    (is (= 1 (or nil 1 (exception))))
    (is (= 1 (or false 1 (exception))))))

(deftest or-returns-first-truthy-test
  (testing "or returns first truthy value"
    (is (= 1 (or nil 1 2)))
    (is (= :first (or :first :second)))
    (is (= 0 (or nil false 0)))) ; 0 is truthy
  (testing "or returns last value if all falsy"
    (is (nil? (or false nil)))   ; returns nil (last)
    (is (false? (or nil false))))) ; returns false (last)

(deftest or-truthiness-test
  (testing "or respects Clojure truthiness"
    ;; 0 is truthy, so or returns it
    (is (= 0 (or 0 :fallback)))
    ;; empty string is truthy
    (is (= "" (or "" :fallback)))
    ;; empty collections are truthy
    (is (= [] (or [] :fallback)))
    (is (= {} (or {} :fallback)))))

;; =============================================================================
;; Combining and/or
;; =============================================================================

(deftest and-or-combined-test
  (testing "and inside or"
    (is (= 3 (or (and 1 2 3) 4)))
    (is (= 4 (or (and nil 2) 4))))
  (testing "or inside and"
    (is (= 2 (and (or nil 1) 2)))
    (is (nil? (and (or nil false) 2)))))

;; =============================================================================
;; Predicates
;; =============================================================================

(deftest nil-predicate-test
  (testing "nil?"
    (is (true? (nil? nil)))
    (is (false? (nil? false)))
    (is (false? (nil? 0)))
    (is (false? (nil? "")))
    (is (false? (nil? [])))))

(deftest some-predicate-test
  (testing "some?"
    ;; some? is the opposite of nil?
    (is (false? (some? nil)))
    (is (true? (some? false))) ; false is NOT nil
    (is (true? (some? 0)))
    (is (true? (some? "")))
    (is (true? (some? [])))))

(deftest true-false-predicates-test
  (testing "true?"
    (is (true? (true? true)))
    (is (false? (true? false)))
    (is (false? (true? nil)))
    (is (false? (true? 1)))    ; 1 is truthy but not true?
    (is (false? (true? :keyword))))
  (testing "false?"
    (is (true? (false? false)))
    (is (false? (false? true)))
    (is (false? (false? nil))) ; nil is falsy but not false?
    (is (false? (false? 0)))))

;; =============================================================================
;; Equality and Identity
;; =============================================================================

(deftest equality-test
  (testing "= with nil"
    (is (true? (= nil nil)))
    (is (false? (= nil false)))
    (is (false? (= nil 0))))
  (testing "= with false"
    (is (true? (= false false)))
    (is (false? (= false nil)))
    (is (false? (= false 0))))
  (testing "= with collections"
    (is (true? (= [] [])))
    (is (true? (= '() []))) ; empty list equals empty vector
    (is (true? (= {} {})))
    (is (true? (= #{} #{})))))

(deftest identical-test
  (testing "identical?"
    (is (true? (identical? nil nil)))
    (is (true? (identical? true true)))
    (is (true? (identical? false false)))
    ;; Keywords are interned
    (is (true? (identical? :a :a)))))

;; =============================================================================
;; if-not, when-not
;; =============================================================================

(deftest if-not-logic-test
  (testing "if-not is inverse of if"
    (is (= :falsy-branch (if-not true :falsy-branch :truthy-branch)))
    (is (= :truthy-branch (if-not false :falsy-branch :truthy-branch)))
    (is (= :truthy-branch (if-not nil :falsy-branch :truthy-branch)))))

(deftest when-not-logic-test
  (testing "when-not executes on falsy"
    (is (= :executed (when-not false :executed)))
    (is (= :executed (when-not nil :executed)))
    (is (nil? (when-not true :executed)))
    (is (nil? (when-not 0 :executed)))) ; 0 is truthy
  (testing "when-not does not evaluate body on truthy"
    (is (nil? (when-not true (exception))))
    (is (nil? (when-not [] (exception))))))

;; =============================================================================
;; if-let, when-let, if-some, when-some
;; =============================================================================

(deftest if-let-logic-test
  (testing "if-let treats false as falsy"
    (is (= :else
           (if-let [x false]
             :then
             :else)))
    (is (= :else
           (if-let [x nil]
             :then
             :else)))
    (is (= :then
           (if-let [x 0]
             :then
             :else)))) ; 0 is truthy
  (testing "binding is available in then branch"
    (is (= 1
           (if-let [x 1]
             x
             :else)))))

(deftest when-let-logic-test
  (testing "when-let treats false as falsy"
    (is (nil? (when-let [x false]
                :body)))
    (is (nil? (when-let [x nil]
                :body)))
    (is (= :body
           (when-let [x 0]
             :body)))))  ; 0 is truthy

(deftest if-some-logic-test
  (testing "if-some only treats nil as falsy"
    (is (= :else
           (if-some [x nil]
             :then
             :else)))
    (is (= :then
           (if-some [x false]
             :then
             :else))) ; false is NOT nil
    (is (= :then
           (if-some [x 0]
             :then
             :else)))))

(deftest when-some-logic-test
  (testing "when-some only treats nil as falsy"
    (is (nil? (when-some [x nil]
                :body)))
    (is (= :body
           (when-some [x false]
             :body))) ; false is NOT nil
    (is (= :body
           (when-some [x 0]
             :body)))))

;; =============================================================================
;; Conditional Threading
;; =============================================================================

(deftest some-threading-test
  (testing "some-> stops on nil"
    (is (nil? (some-> nil
                      inc)))
    (is (nil? (some-> {:a nil}
                      :a
                      inc)))
    (is (= 2
           (some-> 1
                   inc)))
    (is (= 3
           (some-> {:a 1}
                   :a
                   inc
                   inc)))))

(deftest some-threading-falsy-test
  (testing "some->> stops on nil"
    (is (nil? (some->> nil
                       (+ 1))))
    (is (= 3
           (some->> 1
                    (+ 1)
                    (+ 1))))))

(deftest cond-threading-test
  (testing "cond-> conditionally applies"
    (is (= 2 (cond-> 1 true inc)))
    (is (= 1 (cond-> 1 false inc)))
    (is (= 3
           (cond-> 1
             true inc
             true inc)))
    (is (= 2
           (cond-> 1
             true inc
             false inc)))))

;; =============================================================================
;; Logic with Sequences
;; =============================================================================

(deftest empty-seq-truthiness-test
  (testing "empty sequences are truthy"
    ;; This is a common gotcha in Clojure!
    (is (= :truthy (if '() :truthy :falsy)))
    (is (= :truthy (if [] :truthy :falsy))))
  (testing "use seq for empty check"
    ;; (seq coll) returns nil for empty, the seq otherwise
    (is (= :falsy (if (seq []) :truthy :falsy)))
    (is (= :truthy (if (seq [1]) :truthy :falsy)))))

(deftest nil-vs-empty-test
  (testing "nil punning - first/next return nil on empty"
    ;; Use these for nil-punning in loops
    (is (nil? (first [])))
    (is (nil? (next [1])))
    (is (nil? (seq []))))
  (testing "rest returns () which is truthy"
    ;; rest returns empty seq, not nil!
    (is (= '() (rest [1])))
    (is (= :truthy (if (rest [1]) :truthy :falsy)))))

(run-all-tests)
