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

(defn sample-values
  "Returns sample values for testing truthiness and type behaviour.
   Returns a map with :truthy and :falsy keys.

   Usage:
     (:truthy (sample-values))  ; => [true 1 0 -1 ...]
     (:falsy (sample-values))   ; => [nil false]

   Note: Returns fresh data each call to avoid mutation issues."
  []
  {:truthy [true 1 0 -1 0.0 "" "hello" 'symbol :keyword [] [1 2] {} {:a 1} #{}
            #{1}]
   :falsy  [nil false]})

(defn sample-collections
  "Returns sample collections for testing collection operations.
   Returns a map with :lists, :vectors, :maps, and :sets keys.

   Usage:
     (:lists (sample-collections))   ; => ['() '(1) '(1 2 3)]
     (:vectors (sample-collections)) ; => [[] [1] [1 2 3]]

   Note: Returns fresh data each call to avoid mutation issues."
  []
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
     (capture-output #(eval* '(println \"hello\")))

   DECISION: Stub implementation only

   STATUS: Function exists with documented interface but only returns empty string.
   Full implementation BLOCKED pending runtime architecture changes.

   REASON: Klujur's I/O builtins (println, print, etc.) directly call Rust's
   println! macro, which writes to stdout. There is no dynamic *out* binding
   or redirection mechanism like Clojure has.

   IMPLEMENTATION REQUIREMENTS (for future work):
   1. Add a dynamic *out* var to klujur.core (similar to Clojure)
   2. Create a Writer abstraction/protocol in Rust
   3. Modify builtin_print/println in klujur-core/src/builtins/io.rs to:
      - Check for thread-local *out* binding
      - Write to bound writer instead of stdout
      - Fall back to stdout if no binding exists
   4. Provide StringWriter type that accumulates to a String buffer
   5. Update this function to:
      - Create a StringWriter
      - Bind *out* to the writer using (binding [*out* writer] ...)
      - Evaluate thunk
      - Extract accumulated output from writer

   ALTERNATIVES CONSIDERED:
   - Process-level stdout redirection: not thread-safe, affects entire runtime
   - Monkey-patching println: fragile, doesn't work with native functions
   - Output interception via macros: doesn't capture native function output

   CURRENT WORKAROUND: Tests should verify behaviour without checking output,
   or use side-effect patterns like atoms to observe effects."
  [thunk]
  ;; Stub implementation - evaluates thunk but cannot capture output
  {:result (thunk) :output ""})
