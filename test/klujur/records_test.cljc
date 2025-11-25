;; records_test.cljc - Tests for Klujur record operations
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.records-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]))

;; =============================================================================
;; Record Definition
;; =============================================================================

(deftest defrecord-test
  (testing "defrecord creates record type"
    (is (do (defrecord Point [x y])
            true)))
  (testing "positional constructor"
    (is (do (defrecord Point2 [x y])
            (let [p (->Point2 1 2)]
              (= 1 (:x p))))))
  (testing "map constructor"
    (is (do (defrecord Point3 [x y])
            (let [p (map->Point3 {:x 10 :y 20})]
              (= 10 (:x p)))))))

;; =============================================================================
;; Field Access
;; =============================================================================

(deftest field-access-test
  (testing "keyword access"
    (is (= [1 2]
           (do (defrecord FieldTest [a b])
               (let [r (->FieldTest 1 2)]
                 [(:a r) (:b r)])))))
  (testing "get access"
    (is (= 42
           (do (defrecord GetTest [val])
               (let [r (->GetTest 42)]
                 (get r :val))))))
  (testing "get with default"
    (is (= :default
           (do (defrecord DefaultTest [x])
               (let [r (->DefaultTest 1)]
                 (get r :missing :default)))))))

;; =============================================================================
;; Map-like Behaviour
;; =============================================================================

(deftest record-assoc-test
  (testing "assoc on record"
    (is (= [10 2]
           (do (defrecord AssocTest [x y])
               (let [r  (->AssocTest 1 2)
                     r2 (assoc r :x 10)]
                 [(:x r2) (:y r2)])))))
  (testing "assoc new field creates map"
    (is (= 99
           (do (defrecord NewFieldTest [a])
               (let [r  (->NewFieldTest 1)
                     r2 (assoc r :b 99)]
                 (:b r2)))))))

(deftest record-dissoc-test
  (testing "dissoc removes field"
    (is (nil? (do (defrecord DissocTest [x y])
                  (let [r  (->DissocTest 1 2)
                        r2 (dissoc r :x)]
                    (:x r2)))))))

(deftest record-keys-vals-test
  (testing "keys on record"
    (is (= #{:x :y}
           (do (defrecord KeysTest [x y])
               (set (keys (->KeysTest 1 2)))))))
  (testing "vals on record"
    (is (= #{1 2}
           (do (defrecord ValsTest [x y])
               (set (vals (->ValsTest 1 2))))))))

;; =============================================================================
;; Record Equality
;; =============================================================================

(deftest record-equality-test
  (testing "equal records"
    (is (true? (do (defrecord EqTest [a b])
                   (= (->EqTest 1 2) (->EqTest 1 2))))))
  (testing "unequal records - different values"
    (is (false? (do (defrecord EqTest2 [a b])
                    (= (->EqTest2 1 2) (->EqTest2 1 3))))))
  (testing "record not equal to map"
    (is (false? (do (defrecord EqTest3 [a b])
                    (= (->EqTest3 1 2) {:a 1 :b 2}))))))

;; =============================================================================
;; Records with Protocols
;; =============================================================================

(deftest record-protocol-test
  (testing "record implementing protocol"
    (is (= "Point(1, 2)"
           (do (defprotocol IShow
                 (show [x]))
               (defrecord ShowPoint [x y])
               (extend-type ShowPoint
                IShow
                  (show [p] (str "Point(" (:x p) ", " (:y p) ")")))
               (show (->ShowPoint 1 2)))))))

(run-all-tests)
