;; logic_test.cljc - Tests for Klujur logic and truthiness
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.logic-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval* exception]]))

;; =============================================================================
;; Truthiness Fundamentals
;; =============================================================================
;; In Clojure, only nil and false are falsy. Everything else is truthy.

(deftest falsy-values-test
  (testing "nil is falsy"
    (is (= :falsy (eval* "(if nil :truthy :falsy)")))
    (is (false? (eval* "(boolean nil)"))))
  (testing "false is falsy"
    (is (= :falsy (eval* "(if false :truthy :falsy)")))
    (is (false? (eval* "(boolean false)")))))

(deftest truthy-values-test
  (testing "true is truthy"
    (is (= :truthy (eval* "(if true :truthy :falsy)")))
    (is (true? (eval* "(boolean true)"))))
  (testing "numbers are truthy (including zero)"
    (is (= :truthy (eval* "(if 0 :truthy :falsy)")))
    (is (= :truthy (eval* "(if 1 :truthy :falsy)")))
    (is (= :truthy (eval* "(if -1 :truthy :falsy)")))
    (is (= :truthy (eval* "(if 0.0 :truthy :falsy)")))
    (is (= :truthy (eval* "(if 0.1 :truthy :falsy)"))))
  (testing "strings are truthy (including empty)"
    (is (= :truthy (eval* "(if \"\" :truthy :falsy)")))
    (is (= :truthy (eval* "(if \"hello\" :truthy :falsy)"))))
  (testing "collections are truthy (including empty)"
    (is (= :truthy (eval* "(if '() :truthy :falsy)")))
    (is (= :truthy (eval* "(if [] :truthy :falsy)")))
    (is (= :truthy (eval* "(if {} :truthy :falsy)")))
    (is (= :truthy (eval* "(if #{} :truthy :falsy)")))
    (is (= :truthy (eval* "(if [1 2 3] :truthy :falsy)"))))
  (testing "keywords and symbols are truthy"
    (is (= :truthy (eval* "(if :keyword :truthy :falsy)")))
    (is (= :truthy (eval* "(if 'symbol :truthy :falsy)")))))

;; =============================================================================
;; boolean
;; =============================================================================

(deftest boolean-coercion-test
  (testing "boolean coerces to true/false"
    (is (true? (eval* "(boolean true)")))
    (is (false? (eval* "(boolean false)")))
    (is (false? (eval* "(boolean nil)")))
    (is (true? (eval* "(boolean 0)")))
    (is (true? (eval* "(boolean \"\")")))
    (is (true? (eval* "(boolean [])")))
    (is (true? (eval* "(boolean :keyword)")))))

;; =============================================================================
;; not
;; =============================================================================

(deftest not-test
  (testing "not with truthy values"
    (is (false? (eval* "(not true)")))
    (is (false? (eval* "(not 1)")))
    (is (false? (eval* "(not 0)")))    ; 0 is truthy!
    (is (false? (eval* "(not \"\")"))) ; empty string is truthy!
    (is (false? (eval* "(not [])")))   ; empty vector is truthy!
    (is (false? (eval* "(not '())")))  ; empty list is truthy!
    (is (false? (eval* "(not {})")))   ; empty map is truthy!
    (is (false? (eval* "(not #{})")))  ; empty set is truthy!
    (is (false? (eval* "(not :keyword)")))
    (is (false? (eval* "(not 'symbol)"))))
  (testing "not with falsy values"
    (is (true? (eval* "(not nil)")))
    (is (true? (eval* "(not false)")))))

(deftest double-negation-test
  (testing "double negation"
    (is (false? (eval* "(not (not nil))")))
    (is (false? (eval* "(not (not false))")))
    (is (true? (eval* "(not (not true))")))
    (is (true? (eval* "(not (not 0))")))
    (is (true? (eval* "(not (not []))")))))

;; =============================================================================
;; and
;; =============================================================================

(deftest and-basic-test
  (testing "and with no arguments" (is (true? (eval* "(and)"))))
  (testing "and with single argument"
    (is (= 1 (eval* "(and 1)")))
    (is (nil? (eval* "(and nil)")))
    (is (false? (eval* "(and false)"))))
  (testing "and with multiple truthy arguments"
    (is (= 3 (eval* "(and 1 2 3)"))) ; returns last
    (is (= :last (eval* "(and :a :b :last)")))))

(deftest and-short-circuit-test
  (testing "and short-circuits on false"
    (is (false? (eval* "(and false (exception))")))
    (is (false? (eval* "(and true false (exception))"))))
  (testing "and short-circuits on nil"
    (is (nil? (eval* "(and nil (exception))")))
    (is (nil? (eval* "(and true nil (exception))")))))

(deftest and-returns-first-falsy-test
  (testing "and returns first falsy value"
    (is (nil? (eval* "(and nil false)")))
    (is (false? (eval* "(and false nil)")))
    (is (nil? (eval* "(and 1 2 nil 3)")))
    (is (false? (eval* "(and 1 false 2)")))))

(deftest and-truthiness-test
  (testing "and respects Clojure truthiness"
    ;; 0 is truthy, so and continues
    (is (= :yes (eval* "(and 0 :yes)")))
    ;; empty string is truthy
    (is (= :yes (eval* "(and \"\" :yes)")))
    ;; empty collections are truthy
    (is (= :yes (eval* "(and [] :yes)")))
    (is (= :yes (eval* "(and {} :yes)")))
    (is (= :yes (eval* "(and #{} :yes)")))))

;; =============================================================================
;; or
;; =============================================================================

(deftest or-basic-test
  (testing "or with no arguments" (is (nil? (eval* "(or)"))))
  (testing "or with single argument"
    (is (= 1 (eval* "(or 1)")))
    (is (nil? (eval* "(or nil)")))
    (is (false? (eval* "(or false)"))))
  (testing "or with multiple falsy arguments"
    (is (nil? (eval* "(or nil nil nil)")))
    (is (false? (eval* "(or false false)")))
    (is (nil? (eval* "(or nil false nil)")))))  ; returns last evaluated

(deftest or-short-circuit-test
  (testing "or short-circuits on truthy value"
    (is (= 1 (eval* "(or 1 (exception))")))
    (is (= :first (eval* "(or :first (exception))")))
    (is (= 0 (eval* "(or 0 (exception))")))) ; 0 is truthy!
  (testing "or continues past falsy values"
    (is (= 1 (eval* "(or nil 1 (exception))")))
    (is (= 1 (eval* "(or false 1 (exception))")))))

(deftest or-returns-first-truthy-test
  (testing "or returns first truthy value"
    (is (= 1 (eval* "(or nil 1 2)")))
    (is (= :first (eval* "(or :first :second)")))
    (is (= 0 (eval* "(or nil false 0)")))) ; 0 is truthy
  (testing "or returns last value if all falsy"
    (is (nil? (eval* "(or false nil)")))   ; returns nil (last)
    (is (false? (eval* "(or nil false)"))))) ; returns false (last)

(deftest or-truthiness-test
  (testing "or respects Clojure truthiness"
    ;; 0 is truthy, so or returns it
    (is (= 0 (eval* "(or 0 :fallback)")))
    ;; empty string is truthy
    (is (= "" (eval* "(or \"\" :fallback)")))
    ;; empty collections are truthy
    (is (= [] (eval* "(or [] :fallback)")))
    (is (= {} (eval* "(or {} :fallback)")))))

;; =============================================================================
;; Combining and/or
;; =============================================================================

(deftest and-or-combined-test
  (testing "and inside or"
    (is (= 3 (eval* "(or (and 1 2 3) 4)")))
    (is (= 4 (eval* "(or (and nil 2) 4)"))))
  (testing "or inside and"
    (is (= 2 (eval* "(and (or nil 1) 2)")))
    (is (nil? (eval* "(and (or nil false) 2)")))))

;; =============================================================================
;; Predicates
;; =============================================================================

(deftest nil-predicate-test
  (testing "nil?"
    (is (true? (eval* "(nil? nil)")))
    (is (false? (eval* "(nil? false)")))
    (is (false? (eval* "(nil? 0)")))
    (is (false? (eval* "(nil? \"\")")))
    (is (false? (eval* "(nil? [])")))))

(deftest some-predicate-test
  (testing "some?"
    ;; some? is the opposite of nil?
    (is (false? (eval* "(some? nil)")))
    (is (true? (eval* "(some? false)"))) ; false is NOT nil
    (is (true? (eval* "(some? 0)")))
    (is (true? (eval* "(some? \"\")")))
    (is (true? (eval* "(some? [])")))))

(deftest true-false-predicates-test
  (testing "true?"
    (is (true? (eval* "(true? true)")))
    (is (false? (eval* "(true? false)")))
    (is (false? (eval* "(true? nil)")))
    (is (false? (eval* "(true? 1)")))    ; 1 is truthy but not true?
    (is (false? (eval* "(true? :keyword)"))))
  (testing "false?"
    (is (true? (eval* "(false? false)")))
    (is (false? (eval* "(false? true)")))
    (is (false? (eval* "(false? nil)"))) ; nil is falsy but not false?
    (is (false? (eval* "(false? 0)")))))

;; =============================================================================
;; Equality and Identity
;; =============================================================================

(deftest equality-test
  (testing "= with nil"
    (is (true? (eval* "(= nil nil)")))
    (is (false? (eval* "(= nil false)")))
    (is (false? (eval* "(= nil 0)"))))
  (testing "= with false"
    (is (true? (eval* "(= false false)")))
    (is (false? (eval* "(= false nil)")))
    (is (false? (eval* "(= false 0)"))))
  (testing "= with collections"
    (is (true? (eval* "(= [] [])")))
    (is (true? (eval* "(= '() [])"))) ; empty list equals empty vector
    (is (true? (eval* "(= {} {})")))
    (is (true? (eval* "(= #{} #{})")))))

(deftest identical-test
  (testing "identical?"
    (is (true? (eval* "(identical? nil nil)")))
    (is (true? (eval* "(identical? true true)")))
    (is (true? (eval* "(identical? false false)")))
    ;; Keywords are interned
    (is (true? (eval* "(identical? :a :a)")))
    ;; Small integers may be cached (implementation-dependent)
  ))

;; =============================================================================
;; if-not, when-not
;; =============================================================================

(deftest if-not-logic-test
  (testing "if-not is inverse of if"
    (is (= :falsy-branch (eval* "(if-not true :falsy-branch :truthy-branch)")))
    (is (= :truthy-branch
           (eval* "(if-not false :falsy-branch :truthy-branch)")))
    (is (= :truthy-branch
           (eval* "(if-not nil :falsy-branch :truthy-branch)")))))

(deftest when-not-logic-test
  (testing "when-not executes on falsy"
    (is (= :executed (eval* "(when-not false :executed)")))
    (is (= :executed (eval* "(when-not nil :executed)")))
    (is (nil? (eval* "(when-not true :executed)")))
    (is (nil? (eval* "(when-not 0 :executed)")))) ; 0 is truthy
  (testing "when-not does not evaluate body on truthy"
    (is (nil? (eval* "(when-not true (exception))")))
    (is (nil? (eval* "(when-not [] (exception))")))))

;; =============================================================================
;; if-let, when-let, if-some, when-some
;; =============================================================================

(deftest if-let-logic-test
  (testing "if-let treats false as falsy"
    (is (= :else (eval* "(if-let [x false] :then :else)")))
    (is (= :else (eval* "(if-let [x nil] :then :else)")))
    (is (= :then (eval* "(if-let [x 0] :then :else)")))) ; 0 is truthy
  (testing "binding is available in then branch"
    (is (= 1 (eval* "(if-let [x 1] x :else)")))))

(deftest when-let-logic-test
  (testing "when-let treats false as falsy"
    (is (nil? (eval* "(when-let [x false] :body)")))
    (is (nil? (eval* "(when-let [x nil] :body)")))
    (is (= :body (eval* "(when-let [x 0] :body)")))))  ; 0 is truthy

(deftest if-some-logic-test
  (testing "if-some only treats nil as falsy"
    (is (= :else (eval* "(if-some [x nil] :then :else)")))
    (is (= :then (eval* "(if-some [x false] :then :else)"))) ; false is NOT
                                                             ; nil
    (is (= :then (eval* "(if-some [x 0] :then :else)")))))

(deftest when-some-logic-test
  (testing "when-some only treats nil as falsy"
    (is (nil? (eval* "(when-some [x nil] :body)")))
    (is (= :body (eval* "(when-some [x false] :body)"))) ; false is NOT nil
    (is (= :body (eval* "(when-some [x 0] :body)")))))

;; =============================================================================
;; Conditional Threading
;; =============================================================================

(deftest some-threading-test
  (testing "some-> stops on nil"
    (is (nil? (eval* "(some-> nil inc)")))
    (is (nil? (eval* "(some-> {:a nil} :a inc)")))
    (is (= 2 (eval* "(some-> 1 inc)")))
    (is (= 3 (eval* "(some-> {:a 1} :a inc inc)")))))

(deftest some-threading-falsy-test
  (testing "some->> stops on nil"
    (is (nil? (eval* "(some->> nil (+ 1))")))
    (is (= 3 (eval* "(some->> 1 (+ 1) (+ 1))")))))

(deftest cond-threading-test
  (testing "cond-> conditionally applies"
    (is (= 2 (eval* "(cond-> 1 true inc)")))
    (is (= 1 (eval* "(cond-> 1 false inc)")))
    (is (= 3 (eval* "(cond-> 1 true inc true inc)")))
    (is (= 2 (eval* "(cond-> 1 true inc false inc)")))))

;; =============================================================================
;; Logic with Sequences
;; =============================================================================

(deftest empty-seq-truthiness-test
  (testing "empty sequences are truthy"
    ;; This is a common gotcha in Clojure!
    (is (= :truthy (eval* "(if '() :truthy :falsy)")))
    (is (= :truthy (eval* "(if [] :truthy :falsy)"))))
  (testing "use seq for empty check"
    ;; (seq coll) returns nil for empty, the seq otherwise
    (is (= :falsy (eval* "(if (seq []) :truthy :falsy)")))
    (is (= :truthy (eval* "(if (seq [1]) :truthy :falsy)")))))

(deftest nil-vs-empty-test
  (testing "nil punning - first/next return nil on empty"
    ;; Use these for nil-punning in loops
    (is (nil? (eval* "(first [])")))
    (is (nil? (eval* "(next [1])")))
    (is (nil? (eval* "(seq [])"))))
  (testing "rest returns () which is truthy"
    ;; rest returns empty seq, not nil!
    (is (= '() (eval* "(rest [1])")))
    (is (= :truthy (eval* "(if (rest [1]) :truthy :falsy)")))))
