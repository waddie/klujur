;; vars_test.cljc - Tests for Klujur vars and namespaces
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.vars-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; def Basics
;; =============================================================================

(deftest def-basic-test
  (testing "def creates a var with value"
    (is (= 42 (do (def x 42) x)))
    (is (= :value (do (def my-var :value) my-var))))
  (testing "def with expression"
    (is (= 3 (do (def x (+ 1 2)) x)))
    (is (= 10 (do (def x (* 2 5)) x)))))

(deftest def-returns-var-test
  (testing "def returns the var itself"
    (is (var? (def x 1)))
    (is (var? (def y "hello")))))

(deftest def-without-value-test
  (testing "def without value creates unbound var"
    ;; In Clojure, unbound var access throws
    (is (thrown? Exception (do (def x) x))))
  (testing "def without value still creates var" (is (var? (def unbound-var)))))

(deftest def-redefinition-test
  (testing "def can redefine existing var"
    (is (= 2 (do (def x 1) (def x 2) x)))
    (is (= :new (do (def x :old) (def x :new) x)))))

;; =============================================================================
;; def with Docstrings and Metadata
;; =============================================================================

(deftest def-docstring-test
  (testing "def with docstring" (is (= 42 (do (def x "The answer" 42) x))))
  (testing "docstring is accessible via meta"
    (is (= "A documented var"
           (do (def documented "A documented var" 1)
               (:doc (meta #'documented)))))))

(deftest def-metadata-test
  (testing "def with metadata via ^"
    (is (= 42 (do (def ^:private x 42) x)))
    (is (true? (do (def ^:private x 42) (:private (meta #'x))))))
  (testing "def with metadata map"
    (is (= {:custom true}
           (do (def ^{:custom true} x 1) (select-keys (meta #'x) [:custom]))))))

;; =============================================================================
;; var and var?
;; =============================================================================

(deftest var-special-form-test
  (testing "var retrieves the var object"
    (is (var? (do (def x 1) (var x))))
    (is (var? (do (def x 1) #'x)))))

(deftest var-predicate-test
  (testing "var?"
    (is (true? (do (def x 1) (var? #'x))))
    (is (false? (var? 1)))
    (is (false? (var? :keyword)))
    (is (false? (var? nil)))))

(deftest var-deref-test
  (testing "deref on var"
    (is (= 42 (do (def x 42) @#'x)))
    (is (= 42 (do (def x 42) (deref #'x))))))

;; =============================================================================
;; Dynamic Vars and binding
;; =============================================================================

(deftest dynamic-var-test
  (testing "def with ^:dynamic"
    (is (= 1 (do (def ^:dynamic *x* 1) *x*)))
    (is (true? (do (def ^:dynamic *x* 1) (:dynamic (meta #'*x*)))))))

(deftest binding-test
  (testing "binding temporarily rebinds dynamic vars"
    (is (= 2
           (do (def ^:dynamic *x* 1)
               (binding [*x* 2]
                 *x*))))
    (is (= 1
           (do (def ^:dynamic *x* 1)
               (binding [*x* 2]
                 *x*)
               *x*)))) ; original value restored
  (testing "binding with multiple vars"
    (is (= [2 20]
           (do (def ^:dynamic *a* 1)
               (def ^:dynamic *b* 10)
               (binding [*a* 2
                         *b* 20]
                 [*a* *b*]))))))

(deftest binding-nested-test
  (testing "nested binding"
    (is (= 3
           (do (def ^:dynamic *x* 1)
               (binding [*x* 2]
                 (binding [*x* 3]
                   *x*)))))
    (is (= 2
           (do (def ^:dynamic *x* 1)
               (binding [*x* 2]
                 (binding [*x* 3]
                   nil)
                 *x*))))))

(deftest binding-in-function-test
  (testing "binding affects called functions"
    (is (= 2
           (do (def ^:dynamic *x* 1)
               (defn get-x [] *x*)
               (binding [*x* 2]
                 (get-x)))))))

(deftest set!-test
  (testing "set! modifies dynamic var within binding"
    (is (= 10
           (do (def ^:dynamic *x* 1)
               (binding [*x* 5]
                 (set! *x* 10)
                 *x*))))
    (is (= 1
           (do (def ^:dynamic *x* 1)
               (binding [*x* 5]
                 (set! *x* 10))
               *x*)))) ; original restored after binding
  (testing "set! outside binding throws"
    (is (thrown? Exception (do (def ^:dynamic *x* 1) (set! *x* 2))))))

;; =============================================================================
;; alter-var-root
;; =============================================================================

(deftest alter-var-root-test
  (testing "alter-var-root permanently changes var"
    (is (= 2 (do (def x 1) (alter-var-root #'x inc) x)))
    (is (= 10 (do (def x 5) (alter-var-root #'x #(* % 2)) x)))))

;; =============================================================================
;; Var Metadata Functions
;; =============================================================================

(deftest var-get-test
  (testing "var-get" (is (= 42 (do (def x 42) (var-get #'x))))))

(deftest var-set-test
  (testing "var-set within binding"
    (is (= 100
           (do (def ^:dynamic *x* 1)
               (binding [*x* 10]
                 (var-set #'*x* 100)
                 *x*))))))

(deftest with-redefs-test
  (testing "with-redefs temporarily redefines vars"
    (is (= 100
           (do (def x 1)
               (with-redefs [x 100]
                 x))))
    (is (= 1
           (do (def x 1)
               (with-redefs [x 100]
                 nil)
               x)))) ; restored after
  (testing "with-redefs affects all threads (unlike binding)"
    (is (= 100
           (do (def x 1)
               (defn get-x [] x)
               (with-redefs [x 100]
                 (get-x)))))))

;; =============================================================================
;; Namespaces
;; =============================================================================

(deftest ns-test (testing "current namespace" (is (symbol? (ns-name *ns*)))))

(deftest in-ns-test
  (testing "in-ns changes namespace"
    (is (= 'test.ns (do (in-ns 'test.ns) (ns-name *ns*))))))

(deftest resolve-test
  (testing "resolve finds var by symbol"
    (is (var? (resolve '+)))
    (is (nil? (resolve 'nonexistent-var-12345)))))

(deftest ns-resolve-test
  (testing "ns-resolve finds var in specific namespace"
    (is (var? (ns-resolve 'clojure.core '+)))))

;; =============================================================================
;; defonce
;; =============================================================================

(deftest defonce-test
  (testing "defonce only defines once"
    (is (= 1 (do (defonce x 1) (defonce x 2) x))))
  (testing "defonce with unbound var" (is (= 42 (do (defonce y 42) y)))))

;; =============================================================================
;; declare
;; =============================================================================

(deftest declare-test
  (testing "declare creates unbound var" (is (var? (do (declare x) #'x))))
  (testing "declared var can be defined later"
    (is (= 42 (do (declare x) (def x 42) x))))
  (testing "declare multiple vars"
    (is (= [true true] (do (declare a b) [(var? #'a) (var? #'b)])))))

;; =============================================================================
;; defn and defn- (private)
;; =============================================================================

(deftest defn-creates-var-test
  (testing "defn creates a var containing a function"
    (is (var? (do (defn f [] 1) #'f)))
    (is (fn? (do (defn f [] 1) f)))
    (is (= 1 (do (defn f [] 1) (f))))))

(deftest defn-private-test
  (testing "defn- creates private var"
    (is (true? (do (defn- private-fn [] 1) (:private (meta #'private-fn)))))))

;; =============================================================================
;; Var Introspection
;; =============================================================================

(deftest meta-on-var-test
  (testing "meta on var"
    (is (map? (do (def x 1) (meta #'x))))
    (is (contains? (do (def x 1) (meta #'x)) :name))
    (is (contains? (do (def x 1) (meta #'x)) :ns))))

(deftest var-name-test
  (testing "var name from meta" (is (= 'x (do (def x 1) (:name (meta #'x)))))))

(deftest bound-test
  (testing "bound?"
    (is (true? (do (def x 1) (bound? #'x))))
    (is (false? (do (declare y) (bound? #'y))))))

(deftest thread-bound-test
  (testing "thread-bound?"
    (is (false? (do (def ^:dynamic *x* 1) (thread-bound? #'*x*))))
    (is (true? (do (def ^:dynamic *x* 1)
                   (binding [*x* 2]
                     (thread-bound? #'*x*)))))))

;; =============================================================================
;; Namespace Functions - ns-publics and ns-interns
;; =============================================================================
;; NOTE: Tests for ^:private metadata enforcement are in Rust tests
;; because the ^:keyword reader macro is not yet implemented in the parser.

(deftest public-var-qualified-access-test
  (testing "accessing public var via qualified symbol works"
    (is (= 42
           (do (in-ns 'test.pub)
               (def public-val 42)
               (in-ns 'user)
               test.pub/public-val)))))

(run-all-tests)
