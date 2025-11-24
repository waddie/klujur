;; metadata_test.cljc - Tests for Klujur metadata system
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.metadata-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Basic Metadata Operations
;; =============================================================================

(deftest meta-returns-nil-for-values-without-metadata
  (testing "meta returns nil for collections without metadata"
    (is (nil? (eval* "(meta [1 2 3])")))
    (is (nil? (eval* "(meta '(1 2 3))")))
    (is (nil? (eval* "(meta {})")))
    (is (nil? (eval* "(meta #{})")))))

(deftest with-meta-attaches-metadata
  (testing "with-meta attaches metadata to collections"
    (is (= {:a 1} (eval* "(meta (with-meta [1 2] {:a 1}))")))
    (is (= {:b 2} (eval* "(meta (with-meta '(x y) {:b 2}))")))
    (is (= {:c 3} (eval* "(meta (with-meta {:k \"v\"} {:c 3}))")))
    (is (= {:d 4} (eval* "(meta (with-meta #{1 2} {:d 4}))")))))

(deftest with-meta-nil-removes-metadata
  (testing "with-meta nil removes metadata"
    (is (nil? (eval* "(meta (with-meta (with-meta [1] {:a 1}) nil))")))))

;; =============================================================================
;; Metadata Does NOT Affect Equality
;; =============================================================================

(deftest metadata-does-not-affect-equality
  (testing "values with and without metadata are equal"
    (is (eval* "(= [1 2] (with-meta [1 2] {:a 1}))"))
    (is (eval* "(= '(1 2) (with-meta '(1 2) {:b 2}))"))
    (is (eval* "(= {:x 1} (with-meta {:x 1} {:c 3}))"))
    (is (eval* "(= #{1 2} (with-meta #{1 2} {:d 4}))")))
  (testing "two values with different metadata are still equal"
    (is (eval* "(= (with-meta [1 2] {:a 1}) (with-meta [1 2] {:b 2}))"))))

;; =============================================================================
;; Reader Metadata Syntax
;; =============================================================================

(deftest reader-metadata-full-map
  (testing "^{map} form - full metadata map"
    (is (= {:doc "test"} (eval* "(meta ^{:doc \"test\"} [])")))
    (is (= {:private true :doc "secret"}
           (eval* "(meta ^{:private true :doc \"secret\"} {})")))))

(deftest reader-metadata-keyword-shorthand
  (testing "^:keyword form - shorthand for {:keyword true}"
    (is (= {:private true} (eval* "(meta ^:private [])")))
    (is (= {:dynamic true} (eval* "(meta ^:dynamic [])")))))

(deftest reader-metadata-nested
  (testing "nested metadata syntax"
    (is (= {:a 1} (eval* "(meta ^{:a 1} [^{:b 2} [1]])")))))

;; NOTE: ^Symbol form (type hints) not yet fully supported
;; because the symbol in {:tag Symbol} gets evaluated

;; =============================================================================
;; Metadata on Different Types
;; =============================================================================

(deftest metadata-on-collections
  (testing "vectors support metadata"
    (is (= {:type :vec} (eval* "(meta (with-meta [1 2 3] {:type :vec}))"))))
  (testing "lists support metadata"
    (is (= {:type :list} (eval* "(meta (with-meta '(a b c) {:type :list}))"))))
  (testing "maps support metadata"
    (is (= {:type :map} (eval* "(meta (with-meta {:a 1} {:type :map}))"))))
  (testing "sets support metadata"
    (is (= {:type :set} (eval* "(meta (with-meta #{1 2} {:type :set}))"))))
  (testing "symbols support metadata"
    (is (= {:tag :sym} (eval* "(meta (with-meta 'foo {:tag :sym}))")))))

;; =============================================================================
;; Types That Don't Support Metadata
;; =============================================================================

(deftest types-without-metadata-support
  (testing "primitive types return nil from meta"
    (is (nil? (eval* "(meta 42)")))
    (is (nil? (eval* "(meta 3.14)")))
    (is (nil? (eval* "(meta \"string\")")))
    (is (nil? (eval* "(meta :keyword)")))
    (is (nil? (eval* "(meta true)")))
    (is (nil? (eval* "(meta nil)")))))

;; =============================================================================
;; Metadata Access from Collections
;; =============================================================================

(deftest metadata-field-access
  (testing "can access metadata fields using keyword lookup"
    (is (= "a doc string"
           (eval* "(:doc (meta (with-meta [] {:doc \"a doc string\"})))")))
    (is (true? (eval* "(:private (meta (with-meta [] {:private true})))")))))
