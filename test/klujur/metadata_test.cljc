;; metadata_test.cljc - Tests for Klujur metadata system
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

;; =============================================================================
;; Basic Metadata Operations
;; =============================================================================

;; meta returns nil for values without metadata
(= nil (meta [1 2 3]))
(= nil (meta '(1 2 3)))
(= nil (meta {}))
(= nil (meta #{}))

;; with-meta attaches metadata
(= {:a 1} (meta (with-meta [1 2] {:a 1})))
(= {:b 2} (meta (with-meta '(x y) {:b 2})))
(= {:c 3} (meta (with-meta {:k "v"} {:c 3})))
(= {:d 4} (meta (with-meta #{1 2} {:d 4})))

;; with-meta nil removes metadata
(= nil (meta (with-meta (with-meta [1] {:a 1}) nil)))

;; =============================================================================
;; Metadata Does NOT Affect Equality
;; =============================================================================

(= [1 2] (with-meta [1 2] {:a 1}))
(= '(1 2) (with-meta '(1 2) {:b 2}))
(= {:x 1} (with-meta {:x 1} {:c 3}))
(= #{1 2} (with-meta #{1 2} {:d 4}))

;; Two values with different metadata are still equal
(= (with-meta [1 2] {:a 1}) (with-meta [1 2] {:b 2}))

;; =============================================================================
;; Reader Metadata Syntax
;; =============================================================================

;; ^{map} form - full metadata map
(= {:doc "test"} (meta ^{:doc "test"} []))
(= {:private true :doc "secret"} (meta ^{:private true :doc "secret"} {}))

;; ^:keyword form - shorthand for {:keyword true}
(= {:private true} (meta ^:private []))
(= {:dynamic true} (meta ^:dynamic []))

;; Nested metadata syntax
(= {:a 1} (meta ^{:a 1} [^{:b 2} [1]]))

;; NOTE: ^Symbol form (type hints) not yet fully supported
;; because the symbol in {:tag Symbol} gets evaluated

;; =============================================================================
;; Metadata on Different Types
;; =============================================================================

;; Vectors support metadata
(= {:type :vec} (meta (with-meta [1 2 3] {:type :vec})))

;; Lists support metadata
(= {:type :list} (meta (with-meta '(a b c) {:type :list})))

;; Maps support metadata
(= {:type :map} (meta (with-meta {:a 1} {:type :map})))

;; Sets support metadata
(= {:type :set} (meta (with-meta #{1 2} {:type :set})))

;; Symbols support metadata
(= {:tag :sym} (meta (with-meta 'foo {:tag :sym})))

;; =============================================================================
;; Types That Don't Support Metadata
;; =============================================================================

;; These should return nil from meta
(= nil (meta 42))
(= nil (meta 3.14))
(= nil (meta "string"))
(= nil (meta :keyword))
(= nil (meta true))
(= nil (meta nil))

;; =============================================================================
;; Metadata Access from Collections
;; =============================================================================

;; Can access metadata fields using keyword lookup
(= "a doc string" (:doc (meta (with-meta [] {:doc "a doc string"}))))
(= true (:private (meta (with-meta [] {:private true}))))

;; =============================================================================
;; Summary
;; =============================================================================

(println "Metadata tests completed successfully!")
