;; multimethods_test.cljc - Tests for Klujur multimethod operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.multimethods-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Defmulti and Defmethod
;; =============================================================================

(deftest defmulti-test
  (testing "defmulti creates multimethod"
    (is (do (defmulti my-multi type) true)))
  (testing "multimethod is callable"
    (is (do (defmulti callable-multi identity)
            (defmethod callable-multi :test [x] :result)
            (= :result (callable-multi :test))))))

(deftest defmethod-test
  (testing "defmethod adds implementation"
    (is (= :vector
           (do (defmulti type-multi type)
               (defmethod type-multi "vector" [x] :vector)
               (type-multi [1 2 3])))))
  (testing "multiple defmethod implementations"
    (is (= [:string :int :default]
           (do (defmulti multi-impl type)
               (defmethod multi-impl "string" [x] :string)
               (defmethod multi-impl "int" [x] :int)
               (defmethod multi-impl :default [x] :default)
               [(multi-impl "test") (multi-impl 42) (multi-impl :keyword)])))))

(deftest defmethod-default-test
  (testing ":default catches all"
    (is (= :default
           (do (defmulti default-multi identity)
               (defmethod default-multi :default [x] :default)
               (default-multi :anything))))))

;; =============================================================================
;; Hierarchy Functions
;; =============================================================================

(deftest derive-test
  (testing "derive creates relationship"
    (is (true? (do (derive ::child ::parent) (isa? ::child ::parent)))))
  (testing "derive transitive"
    (is (true? (do (derive ::grandchild ::child)
                   (derive ::child ::parent)
                   (isa? ::grandchild ::parent))))))

(deftest underive-test
  (testing "underive removes relationship"
    (is (false? (do (derive ::a ::b) (underive ::a ::b) (isa? ::a ::b))))))

(deftest isa-test
  (testing "isa? with equality" (is (true? (isa? :foo :foo))))
  (testing "isa? with derived"
    (is (true? (do (derive ::x ::y) (isa? ::x ::y)))))
  (testing "isa? negative" (is (false? (isa? :foo :bar)))))

(deftest parents-test
  (testing "parents returns immediate parents"
    (is (= #{::parent} (do (derive ::child ::parent) (parents ::child))))))

(deftest ancestors-test
  (testing "ancestors returns all ancestors"
    (is (= #{::parent ::grandparent}
           (do (derive ::child ::parent)
               (derive ::parent ::grandparent)
               (ancestors ::child))))))

(deftest descendants-test
  (testing "descendants returns all descendants"
    (is (= #{::child ::grandchild}
           (do (derive ::child ::parent)
               (derive ::grandchild ::child)
               (descendants ::parent))))))

;; =============================================================================
;; Prefer-method
;; =============================================================================

(deftest prefer-method-test
  (testing "prefer-method resolves ambiguity"
    (is (= :specific
           (do (defmulti pref-multi (fn [x] [(type x) (:type x)]))
               (derive ::special ::general)
               (defmethod pref-multi ["map" ::general] [x] :general)
               (defmethod pref-multi ["map" ::special] [x] :specific)
               (prefer-method pref-multi ["map" ::special] ["map" ::general])
               (pref-multi {:type ::special}))))))

;; =============================================================================
;; Custom Hierarchies
;; =============================================================================

(deftest custom-hierarchy-test
  (testing "make-hierarchy creates hierarchy"
    (is (hierarchy? (make-hierarchy))))
  (testing "derive with custom hierarchy"
    (is (true? (let [h (-> (make-hierarchy)
                           (derive :child :parent))]
                 (isa? h :child :parent))))))

;; =============================================================================
;; Multimethod Inspection
;; =============================================================================

(deftest methods-test
  (testing "methods returns dispatch map"
    (is (do (defmulti inspect-multi identity)
            (defmethod inspect-multi :a [x] 1)
            (defmethod inspect-multi :b [x] 2)
            (map? (methods inspect-multi))))))

(deftest get-method-test
  (testing "get-method returns method fn"
    (is (do (defmulti get-m-multi identity)
            (defmethod get-m-multi :test [x] :result)
            (fn? (get-method get-m-multi :test))))))

(run-all-tests)
