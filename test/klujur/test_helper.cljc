;; test_helper.cljc - Test utilities for Klujur
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.test-helper)

;; =============================================================================
;; Core Evaluation Utilities
;; =============================================================================

(defn eval*
  "Evaluate a Klujur form or string.
   This is the primary entry point for testing Klujur evaluation.

   Usage:
     (eval* '(+ 1 2))           ; Evaluate a form
     (eval* \"(+ 1 2)\")        ; Evaluate a string
     (eval* {:bindings {'x 10}} '(+ x 1))  ; With context"
  ([form] (if (string? form) (eval (read-string form)) (eval form)))
  ([ctx form]
   ;; With bindings context - wrap in let* with the provided bindings
   (let [bindings      (:bindings ctx)
         binding-pairs (mapcat (fn [[k v]] [k v]) bindings)
         wrapped-form  (list 'let* (vec binding-pairs) form)]
     (eval* wrapped-form))))

(defn eval*-string
  "Evaluate a string as Klujur code.
   Convenience wrapper around eval*."
  [s]
  (eval* s))

;; =============================================================================
;; Exception Testing Utilities
;; =============================================================================

(defn exception
  "Throws an exception. Used to test short-circuit evaluation.
   If this function is called, the test should fail.

   Usage:
     ;; Test that 'and' short-circuits on false
     (eval* '(and false (exception)))  ; Should NOT throw"
  []
  (throw (ex-info "Should not be reached - short-circuit evaluation failed"
                  {})))

(defn throws?
  "Returns true if evaluating the form throws an exception.

   Usage:
     (is (throws? (eval* '(/ 1 0))))"
  [thunk]
  (try (thunk) false (catch :default _ true)))

(defmacro thrown-with-msg?
  "Test that evaluating body throws an exception matching the pattern.

   Usage:
     (is (thrown-with-msg? #\"division by zero\" (eval* '(/ 1 0))))"
  [pattern & body]
  `(try ~@body false (catch :default e# (boolean (re-find ~pattern (str e#))))))

;; =============================================================================
;; Assertion Helpers
;; =============================================================================

(defn submap?
  "Returns true if m1 is a submap of m2 (all keys in m1 exist in m2 with same values).

   Usage:
     (submap? {:a 1} {:a 1 :b 2})  ; => true
     (submap? {:a 1} {:a 2})       ; => false"
  [m1 m2]
  (every? (fn [[k v]] (= v (get m2 k))) m1))

(defn approx=
  "Returns true if two numbers are approximately equal within epsilon.
   Useful for floating-point comparisons.

   Usage:
     (approx= 0.1 0.10000001 0.0001)  ; => true"
  ([a b] (approx= a b 0.00001))
  ([a b epsilon] (< (abs (- a b)) epsilon)))

;; =============================================================================
;; Test Data Generators
;; =============================================================================

;; Sample values for testing truthiness and type behaviour.
(def sample-values
  {:truthy [true 1 0 -1 0.0 "" "hello" 'symbol :keyword [] [1 2] {} {:a 1} #{}
            #{1}]
   :falsy  [nil false]})

;; Sample collections for testing collection operations.
(def sample-collections
  {:lists   ['() '(1) '(1 2 3)]
   :vectors [[] [1] [1 2 3]]
   :maps    [{} {:a 1} {:a 1 :b 2}]
   :sets    [#{} #{1} #{1 2 3}]})

;; =============================================================================
;; Output Capture (for testing side effects)
;; =============================================================================

(defn capture-output
  "Capture stdout during evaluation of thunk.
   Returns {:result <result> :output <string>}

   Usage:
     (capture-output #(eval* '(println \"hello\")))"
  [thunk]
  ;; TODO: Implement output capture when println is available
  {:result (thunk) :output ""})
