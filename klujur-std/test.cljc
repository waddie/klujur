;; klujur-std/test.cljc - Testing framework for Klujur
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.test)

;; =============================================================================
;; State Management
;; =============================================================================

;; Dynamic vars for test execution context
(def ^:dynamic *testing-contexts* [])
(def ^:dynamic *current-test* nil)
(def ^:dynamic *test-results* nil)

;; Global registries
(defonce *tests* (atom {}))
(defonce *fixtures* (atom {}))

;; =============================================================================
;; Result Reporting
;; =============================================================================

(defn print-failure
  "Prints a test failure."
  [{:keys [test contexts expected actual message form]}]
  (println)
  (println "FAIL in" (or test "(unknown)"))
  (when (seq contexts) (println "   " (apply str (interpose " > " contexts))))
  (when message (println "   " message))
  (println "    expected:" (pr-str expected))
  (println "      actual:" (pr-str actual)))

(defn print-error
  "Prints a test error."
  [{:keys [test contexts actual]}]
  (println)
  (println "ERROR in" (or test "(unknown)"))
  (when (seq contexts) (println "   " (apply str (interpose " > " contexts))))
  (println "    error:" (pr-str actual)))

(defn print-summary
  "Prints test run summary."
  [{:keys [pass fail error]}]
  (let [total (+ pass fail error)]
    (println)
    (println "Ran" total "assertions.")
    (println pass "passed," fail "failed," error "errors.")))

(defn report-assertion
  "Records an assertion result and prints failures.
   Note: This is called by the `is` macro, so it must be public."
  [result]
  (let [result (assoc result
                      :test klujur.test/*current-test*
                      :contexts klujur.test/*testing-contexts*)]
    (case (:type result)
      :pass (swap! klujur.test/*test-results* update :pass inc)
      :fail (do (swap! klujur.test/*test-results* update :fail inc)
                (swap! klujur.test/*test-results* update :failures conj result)
                (klujur.test/print-failure result))
      :error (do (swap! klujur.test/*test-results* update :error inc)
                 (swap! klujur.test/*test-results* update :failures conj result)
                 (klujur.test/print-error result)))))

;; =============================================================================
;; Assertion Macros
;; =============================================================================

(defmacro is
  "Assert that form is truthy. Supports special forms for equality and exceptions.

   Examples:
     (is true)
     (is (= 4 (+ 2 2)))
     (is (thrown? Exception (throw \"error\")))
     (is (thrown-with-msg? \"pattern\" (throw \"pattern in message\")))"
  ([form] `(klujur.test/is ~form nil))
  ([form msg]
   (cond
     ;; (is (= expected actual))
     (and (seq? form) (= '= (first form)))
     (let [[_ expected actual] form]
       `(let [expected# ~expected
              actual#   ~actual
              pass?#    (= expected# actual#)]
          (klujur.test/report-assertion {:type     (if pass?# :pass :fail)
                                         :expected expected#
                                         :actual   actual#
                                         :message  ~msg
                                         :form     '~form})
          pass?#))
     ;; (is (thrown? ExType body...))
     (and (seq? form) (= 'thrown? (first form)))
     (let [[_ ex-type & body] form]
       `(try (do ~@body)
             (klujur.test/report-assertion {:type     :fail
                                            :expected '(~'thrown? ~ex-type)
                                            :actual   "No exception thrown"
                                            :form     '~form})
             false
             (catch :default e#
               (klujur.test/report-assertion
                {:type :pass :expected '~ex-type :actual e# :form '~form})
               true)))
     ;; (is (thrown-with-msg? "pattern" body...))
     (and (seq? form) (= 'thrown-with-msg? (first form)))
     (let [[_ pattern & body] form]
       `(try (do ~@body)
             (klujur.test/report-assertion
              {:type     :fail
               :expected (str "Exception with message containing: " ~pattern)
               :actual   "No exception thrown"
               :form     '~form})
             false
             (catch :default e#
               (let [emsg#   (or (ex-message e#) (str e#))
                     match?# (includes? emsg# ~pattern)]
                 (klujur.test/report-assertion
                  {:type     (if match?# :pass :fail)
                   :expected (str "Message containing: " ~pattern)
                   :actual   emsg#
                   :form     '~form})
                 match?#))))
     ;; Default: (is expr)
     :else `(let [result# ~form]
              (klujur.test/report-assertion {:type     (if result# :pass :fail)
                                             :expected '~form
                                             :actual   result#
                                             :message  ~msg
                                             :form     '~form})
              (boolean result#)))))

(defmacro testing
  "Adds a context description to test failures."
  [description & body]
  `(binding [klujur.test/*testing-contexts* (conj klujur.test/*testing-contexts*
                                                  ~description)]
     ~@body))

(defmacro are
  "Checks multiple test cases using a template.

   Example:
     (are [x y] (= x y)
       2 (+ 1 1)
       4 (* 2 2))"
  [argv expr & args]
  (let [n      (count argv)
        chunks (partition n args)]
    `(do ~@(for [vals chunks]
             `(let [~@(interleave argv vals)]
                (klujur.test/is ~expr))))))

;; =============================================================================
;; Test Definition
;; =============================================================================

(defmacro deftest
  "Defines a test function with no arguments."
  [name & body]
  (let [ns-sym (symbol (str *ns*))]
    `(do (defn ~name
           []
           (binding [klujur.test/*current-test*     '~name
                     klujur.test/*testing-contexts* []]
             ~@body))
         (swap! klujur.test/*tests* update '~ns-sym assoc '~name ~name)
         (var ~name))))

;; =============================================================================
;; Fixtures
;; =============================================================================

(defn use-fixtures
  "Registers fixtures for the current namespace.
   Type is :once (run once per ns) or :each (run around each test).
   Fixtures are functions that take a thunk and call it."
  [type & fns]
  (let [ns-sym (symbol (str *ns*))]
    (swap! klujur.test/*fixtures* update
      ns-sym
      (fn [m] (update (or m {}) type (fnil into []) fns)))))

(defn apply-fixtures
  "Applies fixtures in order, calling body-fn in the innermost context."
  [fixtures body-fn]
  (if (empty? fixtures)
    (body-fn)
    (let [[f & rest-fns] fixtures]
      (f #(klujur.test/apply-fixtures rest-fns body-fn)))))

;; =============================================================================
;; Test Execution
;; =============================================================================

(defn run-namespace-tests
  "Runs all tests in a namespace with fixtures."
  [ns-sym tests]
  (let [{:keys [once each]} (get @klujur.test/*fixtures* ns-sym {})]
    (klujur.test/apply-fixtures (or once [])
                                (fn []
                                  (doseq [[test-name test-fn] tests]
                                    (klujur.test/apply-fixtures
                                     (or each [])
                                     (fn []
                                       (try (test-fn)
                                            (catch :default e
                                              (klujur.test/report-assertion
                                               {:type     :error
                                                :test     test-name
                                                :actual   e
                                                :expected "No error"}))))))))))

(defn run-tests
  "Runs tests in the specified namespaces, or all namespaces if none specified.
   Returns a map with :pass, :fail, :error counts and :failures list."
  [& ns-syms]
  (let [namespaces (if (seq ns-syms) ns-syms (keys @klujur.test/*tests*))]
    (binding [klujur.test/*test-results*
              (atom {:pass 0 :fail 0 :error 0 :failures []})]
      (doseq [ns-sym namespaces]
        (when-let [tests (get @klujur.test/*tests* ns-sym)]
          (println)
          (println "Testing" ns-sym)
          (klujur.test/run-namespace-tests ns-sym tests)))
      (klujur.test/print-summary @klujur.test/*test-results*)
      @klujur.test/*test-results*)))

(defn run-all-tests
  "Runs all registered tests."
  []
  (apply klujur.test/run-tests (keys @klujur.test/*tests*)))
