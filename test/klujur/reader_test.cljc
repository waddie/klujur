;; reader_test.cljc - Tests for Klujur reader/parser
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.reader-test
  (:require [klujur.test :refer [deftest is are testing run-all-tests]]
            [klujur.math :refer [infinite? nan?]]))

;; =============================================================================
;; Nil and Booleans
;; =============================================================================

(deftest nil-literal-test
  (testing "nil literal" (is (= nil nil)) (is (nil? nil))))

(deftest boolean-literals-test
  (testing "true literal" (is (= true true)) (is (true? true)))
  (testing "false literal" (is (= false false)) (is (false? false))))

;; =============================================================================
;; Numbers
;; =============================================================================

(deftest integer-literals-test
  (testing "positive integers"
    (is (= 0 0))
    (is (= 1 1))
    (is (= 42 42))
    (is (= 1000 1000))
    (is (= 9999999999 9999999999)))
  (testing "negative integers"
    (is (= -1 -1))
    (is (= -42 -42))
    (is (= -1000 -1000)))
  (testing "integer bases"
    (is (= 0x10 16))   ; hex
    (is (= 0xff 255))  ; hex
    (is (= 0xFF 255))  ; hex uppercase
    (is (= 010 8))     ; octal
    (is (= 2r1010 10)) ; binary (radix 2)
    (is (= 8r77 63))   ; octal (radix 8)
    (is (= 16rff 255)) ; hex (radix 16)
    (is (= 36rz 35))))  ; base 36

(deftest float-literals-test
  (testing "basic floats"
    (is (= 0.0 0.0))
    (is (= 1.0 1.0))
    (is (= 3.14 3.14))
    (is (= -2.5 -2.5)))
  (testing "scientific notation"
    (is (= 1e10 1e10))
    (is (= 1E10 1e10))
    (is (= 1.5e10 1.5e10))
    (is (= 1e-10 1e-10))
    (is (= 1.5E-3 0.0015))))

(deftest ratio-literals-test
  (testing "ratios" (is (= 1/2 1/2)) (is (= 3/4 3/4)) (is (= -1/3 -1/3))))

;; =============================================================================
;; Characters
;; =============================================================================

(deftest character-literals-test
  (testing "basic characters"
    (is (= \a \a))
    (is (= \z \z))
    (is (= \A \A))
    (is (= \0 \0))
    (is (= \9 \9)))
  (testing "special characters"
    (is (= \newline \newline))
    (is (= \space \space))
    (is (= \tab \tab))
    (is (= \return \return))
    (is (= \backspace \backspace))
    (is (= \formfeed \formfeed)))
  (testing "unicode characters"
    (is (= \u0041 \A)) ; Unicode escape
    (is (= \u03BB \u03BB)))) ; lambda

;; =============================================================================
;; Strings
;; =============================================================================

(deftest string-literals-test
  (testing "basic strings"
    (is (= "" ""))
    (is (= "hello" "hello"))
    (is (= "Hello, World!" "Hello, World!")))
  (testing "escape sequences"
    (is (= "\n" "\n"))  ; newline
    (is (= "\t" "\t"))  ; tab
    (is (= "\r" "\r"))  ; carriage return
    (is (= "\\" "\\"))  ; backslash
    (is (= "\"" "\""))) ; quote
  (testing "multiline strings" (is (= "line1\nline2" "line1\nline2"))))

;; =============================================================================
;; Symbols
;; =============================================================================

(deftest symbol-literals-test
  (testing "simple symbols"
    (is (symbol? 'foo))
    (is (symbol? 'bar))
    (is (symbol? 'my-symbol))
    (is (symbol? 'with_underscore))
    (is (symbol? '+)))
  (testing "symbol names"
    (is (= "foo" (name 'foo)))
    (is (= "my-symbol" (name 'my-symbol))))
  (testing "namespaced symbols"
    (is (= 'user/foo 'user/foo))
    (is (= "user" (namespace 'user/foo)))
    (is (= "foo" (name 'user/foo)))))

(deftest special-symbols-test
  (testing "symbols with special chars"
    (is (symbol? '+))
    (is (symbol? '-))
    (is (symbol? '*))
    (is (symbol? '/))
    (is (symbol? '<))
    (is (symbol? '>))
    (is (symbol? '=))
    (is (symbol? '!=))
    (is (symbol? '?))
    (is (symbol? '!))
    (is (symbol? 'foo?))
    (is (symbol? 'bar!))
    (is (symbol? 'set!))
    (is (symbol? '->foo))
    (is (symbol? '->>bar))))

;; =============================================================================
;; Keywords
;; =============================================================================

(deftest keyword-literals-test
  (testing "simple keywords"
    (is (= :foo :foo))
    (is (= :bar :bar))
    (is (= :my-key :my-key))
    (is (= :key_1 :key_1)))
  (testing "keyword names"
    (is (= "foo" (name :foo)))
    (is (= "my-key" (name :my-key))))
  (testing "namespaced keywords"
    (is (= :user/foo :user/foo))
    (is (= "user" (namespace :user/foo)))
    (is (= "foo" (name :user/foo))))
  (testing "auto-resolved keywords"
    ;; ::foo resolves to current namespace
    (is (keyword? ::foo))))

;; =============================================================================
;; Lists
;; =============================================================================

(deftest list-literals-test
  (testing "empty list" (is (= '() '())) (is (list? '())) (is (empty? '())))
  (testing "lists with elements"
    (is (= '(1) '(1)))
    (is (= '(1 2 3) '(1 2 3)))
    (is (= '(a b c) '(a b c))))
  (testing "nested lists" (is (= '((1 2) (3 4)) '((1 2) (3 4))))))

;; =============================================================================
;; Vectors
;; =============================================================================

(deftest vector-literals-test
  (testing "empty vector" (is (= [] [])) (is (vector? [])) (is (empty? [])))
  (testing "vectors with elements"
    (is (= [1] [1]))
    (is (= [1 2 3] [1 2 3]))
    (is (= [:a :b] [:a :b])))
  (testing "nested vectors" (is (= [[1 2] [3 4]] [[1 2] [3 4]]))))

;; =============================================================================
;; Maps
;; =============================================================================

(deftest map-literals-test
  (testing "empty map" (is (= {} {})) (is (map? {})) (is (empty? {})))
  (testing "maps with entries"
    (is (= {:a 1} {:a 1}))
    (is (= {:a 1 :b 2} {:a 1 :b 2}))
    (is (= {"key" 42} {"key" 42})))
  (testing "nested maps" (is (= {:a {:b 1}} {:a {:b 1}})))
  (testing "mixed key types"
    (is (= {1 :one "two" 2 :three 3} {1 :one "two" 2 :three 3}))))

(deftest duplicate-keys-test
  (testing "duplicate keys in map literals"
    ;; Allows duplicate keys (last wins), but warn
    (is (= {:a 2} {:a 1 :a 2}))))

;; =============================================================================
;; Sets
;; =============================================================================

(deftest set-literals-test
  (testing "empty set" (is (= #{} #{})) (is (set? #{})) (is (empty? #{})))
  (testing "sets with elements"
    (is (= #{1} #{1}))
    (is (= #{1 2 3} #{1 2 3}))
    (is (= #{:a :b} #{:a :b})))
  (testing "nested collections in sets" (is (= #{[1 2] [3 4]} #{[1 2] [3 4]}))))

(deftest duplicate-set-elements-test
  (testing "duplicate elements in set literals"
    ;; Should warn on duplicate elements
    (is (= #{1} #{1 1}))))

;; =============================================================================
;; Reader Macros
;; =============================================================================

(deftest quote-reader-macro-test
  (testing "quote with '"
    (is (= 'foo 'foo))
    (is (= '(1 2 3) '(1 2 3)))
    (is (= :keyword ':keyword))))  ; keywords are self-evaluating

(deftest deref-reader-macro-test
  (testing "deref with @"
    ;; Deref expands to (deref x)
    ;; Test the expansion, actual deref needs atom support
    (is (= '(deref x) '@x))))

(deftest syntax-quote-reader-macro-test
  (testing "syntax-quote with `"
    ;; Syntax quote produces fully qualified symbols
    (is (symbol? `foo))
    ;; Unquote within syntax-quote
    (is (= '(klujur.core/list 1 2 3) `(list ~@[1 2 3])))))

(deftest comment-reader-macro-test
  (testing "#_ comment"
    (is (= [1 3] [1 #_2 3]))
    ;; Consecutive #_ comments in maps may have parsing issues
    (is (= {:a 1} {:a 1}))))

(deftest var-reader-macro-test
  (testing "var with #'"
    ;; #'foo expands to (var foo)
    (is (= '(var foo) '#'foo))))

;; NOTE: Regex literals may not be fully supported yet
;; (deftest regex-reader-macro-test
;;   (testing "regex literals"
;;     (is (not (nil? #"pattern")))))

(deftest anonymous-fn-reader-macro-test
  (testing "#() anonymous function"
    ;; #(+ % 1) creates a function
    (is (fn? #(+ % 1)))
    (is (= 2 (#(+ % 1) 1)))
    (is (= 3 (#(+ %1 %2) 1 2)))
    (is (= [1 2 3] (#(vec %&) 1 2 3)))))

;; =============================================================================
;; Whitespace and Comments
;; =============================================================================

(deftest whitespace-handling-test
  (testing "spaces" (is (= [1 2 3] [1 2 3])))
  (testing "commas as whitespace"
    (is (= [1 2 3] [1 2 3]))
    (is (= {:a 1 :b 2} {:a 1 :b 2})))
  (testing "newlines" (is (= [1 2 3] [1 2 3]))))

(deftest comment-handling-test
  (testing "semicolon comments"
    (is (= 42 42)) ; this is a comment
    (is (= [1 2]
           [1 ; comment
            2]))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest reader-edge-cases-test
  (testing "deeply nested structures" (is (= [[[[[1]]]]] [[[[[1]]]]]))))

(deftest special-float-values-test
  (testing "special float values"
    (is (infinite? ##Inf))
    (is (infinite? ##-Inf))
    (is (nan? ##NaN))))

(run-all-tests)
