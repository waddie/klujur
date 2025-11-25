;; metadata_test.cljc - Tests for Klujur metadata system
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.metadata-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Basic Metadata Operations
;; =============================================================================

(deftest meta-returns-nil-for-values-without-metadata
  (testing "meta returns nil for collections without metadata"
    (is (nil? (meta [1 2 3])))
    (is (nil? (meta '(1 2 3))))
    (is (nil? (meta {})))
    (is (nil? (meta #{})))))

(deftest with-meta-attaches-metadata
  (testing "with-meta attaches metadata to collections"
    (is (= {:a 1} (meta (with-meta [1 2] {:a 1}))))
    (is (= {:b 2} (meta (with-meta '(x y) {:b 2}))))
    (is (= {:c 3} (meta (with-meta {:k "v"} {:c 3}))))
    (is (= {:d 4} (meta (with-meta #{1 2} {:d 4}))))))

(deftest with-meta-nil-removes-metadata
  (testing "with-meta nil removes metadata"
    (is (nil? (meta (with-meta (with-meta [1] {:a 1}) nil))))))

;; =============================================================================
;; Metadata Does NOT Affect Equality
;; =============================================================================

(deftest metadata-does-not-affect-equality
  (testing "values with and without metadata are equal"
    (is (= [1 2] (with-meta [1 2] {:a 1})))
    (is (= '(1 2) (with-meta '(1 2) {:b 2})))
    (is (= {:x 1} (with-meta {:x 1} {:c 3})))
    (is (= #{1 2} (with-meta #{1 2} {:d 4}))))
  (testing "two values with different metadata are still equal"
    (is (= (with-meta [1 2] {:a 1}) (with-meta [1 2] {:b 2})))))

;; =============================================================================
;; Reader Metadata Syntax
;; =============================================================================

(deftest reader-metadata-full-map
  (testing "^{map} form - full metadata map"
    (is (= {:doc "test"} (meta ^{:doc "test"} [])))
    (is (= {:private true :doc "secret"}
           (meta ^{:private true :doc "secret"} {})))))

(deftest reader-metadata-keyword-shorthand
  (testing "^:keyword form - shorthand for {:keyword true}"
    (is (= {:private true} (meta ^:private [])))
    (is (= {:dynamic true} (meta ^:dynamic [])))))

(deftest reader-metadata-nested
  (testing "nested metadata syntax"
    (is (= {:a 1} (meta ^{:a 1} [^{:b 2} [1]])))))

;; NOTE: ^Symbol form (type hints) not yet fully supported
;; because the symbol in {:tag Symbol} gets evaluated

;; =============================================================================
;; Metadata on Different Types
;; =============================================================================

(deftest metadata-on-collections
  (testing "vectors support metadata"
    (is (= {:type :vec} (meta (with-meta [1 2 3] {:type :vec})))))
  (testing "lists support metadata"
    (is (= {:type :list} (meta (with-meta '(a b c) {:type :list})))))
  (testing "maps support metadata"
    (is (= {:type :map} (meta (with-meta {:a 1} {:type :map})))))
  (testing "sets support metadata"
    (is (= {:type :set} (meta (with-meta #{1 2} {:type :set})))))
  (testing "symbols support metadata"
    (is (= {:tag :sym} (meta (with-meta 'foo {:tag :sym}))))))

;; =============================================================================
;; Types That Don't Support Metadata
;; =============================================================================

(deftest types-without-metadata-support
  (testing "primitive types return nil from meta"
    (is (nil? (meta 42)))
    (is (nil? (meta 3.14)))
    (is (nil? (meta "string")))
    (is (nil? (meta :keyword)))
    (is (nil? (meta true)))
    (is (nil? (meta nil)))))

;; =============================================================================
;; Metadata Access from Collections
;; =============================================================================

(deftest metadata-field-access
  (testing "can access metadata fields using keyword lookup"
    (is (= "a doc string" (:doc (meta (with-meta [] {:doc "a doc string"})))))
    (is (true? (:private (meta (with-meta [] {:private true})))))))

;; =============================================================================
;; vary-meta
;; =============================================================================

(deftest vary-meta-test
  (testing "vary-meta applies function to metadata"
    (is (= {:a 2} (meta (vary-meta (with-meta [] {:a 1}) update :a inc)))))
  (testing "vary-meta with additional args"
    (is (= {:a 1 :b 2} (meta (vary-meta (with-meta [] {:a 1}) assoc :b 2)))))
  (testing "vary-meta preserves collection value"
    (is (= [1 2 3] (vary-meta (with-meta [1 2 3] {:a 1}) assoc :b 2))))
  (testing "vary-meta on value without metadata"
    (is (= {:new true} (meta (vary-meta [] assoc :new true))))))

;; =============================================================================
;; alter-meta!
;; =============================================================================

(deftest alter-meta-test
  (testing "alter-meta! modifies var metadata"
    (is (= {:doc "updated"}
           (do (def ^{:doc "original"} test-var 1)
               (alter-meta! #'test-var assoc :doc "updated")
               (select-keys (meta #'test-var) [:doc])))))
  (testing "alter-meta! with additional args"
    (is (= {:count 2}
           (do (def ^{:count 1} counter-var 0)
               (alter-meta! #'counter-var update :count inc)
               (select-keys (meta #'counter-var) [:count]))))))

(run-all-tests)
