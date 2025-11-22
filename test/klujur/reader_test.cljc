;; reader_test.cljc - Tests for Klujur reader/parser
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

(ns klujur.reader-test
  (:require [clojure.test :refer [deftest is are testing]]
            [klujur.test-helper :refer [eval*]]))

;; =============================================================================
;; Nil and Booleans
;; =============================================================================

(deftest nil-literal-test
  (testing "nil literal" (is (= nil (eval* "nil"))) (is (nil? (eval* "nil")))))

(deftest boolean-literals-test
  (testing "true literal"
    (is (= true (eval* "true")))
    (is (true? (eval* "true"))))
  (testing "false literal"
    (is (= false (eval* "false")))
    (is (false? (eval* "false")))))

;; =============================================================================
;; Numbers
;; =============================================================================

(deftest integer-literals-test
  (testing "positive integers"
    (are [s v] (= v (eval* s))
     "0"          0
     "1"          1
     "42"         42
     "1000"       1000
     "9999999999" 9999999999))
  (testing "negative integers"
    (are [s v] (= v (eval* s))
     "-1"    -1
     "-42"   -42
     "-1000" -1000))
  (testing "integer bases"
    (are [s v] (= v (eval* s))
     "0x10"   16  ; hex
     "0xff"   255 ; hex
     "0xFF"   255 ; hex uppercase
     "010"    8   ; octal
     "2r1010" 10  ; binary (radix 2)
     "8r77"   63  ; octal (radix 8)
     "16rff"  255 ; hex (radix 16)
     "36rz"   35)))   ; base 36

(deftest float-literals-test
  (testing "basic floats"
    (are [s v] (= v (eval* s))
     "0.0"  0.0
     "1.0"  1.0
     "3.14" 3.14
     "-2.5" -2.5))
  (testing "scientific notation"
    (are [s v] (= v (eval* s))
     "1e10"   1e10
     "1E10"   1e10
     "1.5e10" 1.5e10
     "1e-10"  1e-10
     "1.5E-3" 0.0015)))

(deftest ratio-literals-test
  (testing "ratios"
    (is (= 1/2 (eval* "1/2")))
    (is (= 3/4 (eval* "3/4")))
    (is (= -1/3 (eval* "-1/3")))))

;; =============================================================================
;; Characters
;; =============================================================================

(deftest character-literals-test
  (testing "basic characters"
    (are [s v] (= v (eval* s))
     "\\a" \a
     "\\z" \z
     "\\A" \A
     "\\0" \0
     "\\9" \9))
  (testing "special characters"
    (are [s v] (= v (eval* s))
     "\\newline"   \newline
     "\\space"     \space
     "\\tab"       \tab
     "\\return"    \return
     "\\backspace" \backspace
     "\\formfeed"  \formfeed))
  (testing "unicode characters"
    (are [s v] (= v (eval* s))
     "\\u0041" \A ; Unicode escape
     "\\u03BB" \u03BB))) ; lambda

;; =============================================================================
;; Strings
;; =============================================================================

(deftest string-literals-test
  (testing "basic strings"
    (are [s v] (= v (eval* s))
     "\"\""      ""
     "\"hello\"" "hello"
     "\"Hello, World!\"" "Hello, World!"))
  (testing "escape sequences"
    (are [s v] (= v (eval* s))
     "\"\\n\""  "\n"   ; newline
     "\"\\t\""  "\t"   ; tab
     "\"\\r\""  "\r"   ; carriage return
     "\"\\\\\"" "\\"   ; backslash
     "\"\\\"\"" "\"")) ; quote
  (testing "multiline strings"
    (is (= "line1\nline2" (eval* "\"line1\nline2\"")))))

;; =============================================================================
;; Symbols
;; =============================================================================

(deftest symbol-literals-test
  (testing "simple symbols"
    (are [s] (symbol? (eval* (str "'" s)))
     "foo"
     "bar"
     "my-symbol"
     "with_underscore"
     "+"))
  (testing "symbol names"
    (are [s n] (= n (name (eval* (str "'" s))))
     "foo"       "foo"
     "my-symbol" "my-symbol"))
  (testing "namespaced symbols"
    (is (= 'user/foo (eval* "'user/foo")))
    (is (= "user" (namespace (eval* "'user/foo"))))
    (is (= "foo" (name (eval* "'user/foo"))))))

(deftest special-symbols-test
  (testing "symbols with special chars"
    (are [s] (symbol? (eval* (str "'" s)))
     "+"
     "-"
     "*"
     "/"
     "<"
     ">"
     "="
     "!="
     "?"
     "!"
     "foo?"
     "bar!"
     "set!"
     "->foo"
     "->>bar")))

;; =============================================================================
;; Keywords
;; =============================================================================

(deftest keyword-literals-test
  (testing "simple keywords"
    (are [s v] (= v (eval* s))
     ":foo"    :foo
     ":bar"    :bar
     ":my-key" :my-key
     ":key_1"  :key_1))
  (testing "keyword names"
    (are [s n] (= n (name (eval* s)))
     ":foo"    "foo"
     ":my-key" "my-key"))
  (testing "namespaced keywords"
    (is (= :user/foo (eval* ":user/foo")))
    (is (= "user" (namespace (eval* ":user/foo"))))
    (is (= "foo" (name (eval* ":user/foo")))))
  (testing "auto-resolved keywords"
    ;; ::foo resolves to current namespace
    (is (keyword? (eval* "::foo")))))

;; =============================================================================
;; Lists
;; =============================================================================

(deftest list-literals-test
  (testing "empty list"
    (is (= '() (eval* "'()")))
    (is (list? (eval* "'()")))
    (is (empty? (eval* "'()"))))
  (testing "lists with elements"
    (are [s v] (= v (eval* s))
     "'(1)"     '(1)
     "'(1 2 3)" '(1 2 3)
     "'(a b c)" '(a b c)))
  (testing "nested lists" (is (= '((1 2) (3 4)) (eval* "'((1 2) (3 4))")))))

;; =============================================================================
;; Vectors
;; =============================================================================

(deftest vector-literals-test
  (testing "empty vector"
    (is (= [] (eval* "[]")))
    (is (vector? (eval* "[]")))
    (is (empty? (eval* "[]"))))
  (testing "vectors with elements"
    (are [s v] (= v (eval* s))
     "[1]"     [1]
     "[1 2 3]" [1 2 3]
     "[:a :b]" [:a :b]))
  (testing "nested vectors" (is (= [[1 2] [3 4]] (eval* "[[1 2] [3 4]]")))))

;; =============================================================================
;; Maps
;; =============================================================================

(deftest map-literals-test
  (testing "empty map"
    (is (= {} (eval* "{}")))
    (is (map? (eval* "{}")))
    (is (empty? (eval* "{}"))))
  (testing "maps with entries"
    (are [s v] (= v (eval* s))
     "{:a 1}"       {:a 1}
     "{:a 1 :b 2}"  {:a 1 :b 2}
     "{\"key\" 42}" {"key" 42}))
  (testing "nested maps" (is (= {:a {:b 1}} (eval* "{:a {:b 1}}"))))
  (testing "mixed key types"
    (is (= {1 :one "two" 2 :three 3} (eval* "{1 :one \"two\" 2 :three 3}")))))

(deftest duplicate-keys-test
  (testing "duplicate keys in map literals"
    ;; Allows duplicate keys (last wins), but warn
    (is (= {:a 2} (eval* "{:a 1 :a 2}")))))

;; =============================================================================
;; Sets
;; =============================================================================

(deftest set-literals-test
  (testing "empty set"
    (is (= #{} (eval* "#{}")))
    (is (set? (eval* "#{}")))
    (is (empty? (eval* "#{}"))))
  (testing "sets with elements"
    (are [s v] (= v (eval* s))
     "#{1}"     #{1}
     "#{1 2 3}" #{1 2 3}
     "#{:a :b}" #{:a :b}))
  (testing "nested collections in sets"
    (is (= #{[1 2] [3 4]} (eval* "#{[1 2] [3 4]}")))))

(deftest duplicate-set-elements-test
  (testing "duplicate elements in set literals"
    ;; Should warn on duplicate elements
    (is (= #{1} (eval* "#{1 1}")))))

;; =============================================================================
;; Reader Macros
;; =============================================================================

(deftest quote-reader-macro-test
  (testing "quote with '"
    (are [s v] (= v (eval* s))
     "'foo"      'foo
     "'(1 2 3)"  '(1 2 3)
     "':keyword" :keyword)))  ; keywords are self-evaluating

(deftest deref-reader-macro-test
  (testing "deref with @"
    ;; Deref expands to (deref x)
    ;; Test the expansion, actual deref needs atom support
    (is (= '(deref x) (eval* "'@x")))))

(deftest syntax-quote-reader-macro-test
  (testing "syntax-quote with `"
    ;; Syntax quote produces fully qualified symbols
    (is (symbol? (eval* "`foo")))
    ;; Unquote within syntax-quote
    (is (= '(clojure.core/list 1 2 3) (eval* "`(list ~@[1 2 3])")))))

(deftest comment-reader-macro-test
  (testing "#_ comment"
    (is (= [1 3] (eval* "[1 #_2 3]")))
    (is (= {:a 1} (eval* "{:a 1 #_:b #_2}")))))

(deftest var-reader-macro-test
  (testing "var with #'"
    ;; #'foo expands to (var foo)
    (is (= '(var foo) (eval* "'#'foo")))))

(deftest regex-reader-macro-test
  (testing "regex literals"
    (is (= (type #"pattern") (type (eval* "#\"pattern\""))))))

(deftest anonymous-fn-reader-macro-test
  (testing "#() anonymous function"
    ;; #(+ % 1) creates a function
    (is (fn? (eval* "#(+ % 1)")))
    (is (= 2 ((eval* "#(+ % 1)") 1)))
    (is (= 3 ((eval* "#(+ %1 %2)") 1 2)))
    (is (= [1 2 3] ((eval* "#(vec %&)") 1 2 3)))))

;; =============================================================================
;; Whitespace and Comments
;; =============================================================================

(deftest whitespace-handling-test
  (testing "spaces" (is (= [1 2 3] (eval* "[1   2   3]"))))
  (testing "commas as whitespace"
    (is (= [1 2 3] (eval* "[1, 2, 3]")))
    (is (= {:a 1 :b 2} (eval* "{:a 1, :b 2}"))))
  (testing "newlines" (is (= [1 2 3] (eval* "[1\n2\n3]")))))

(deftest comment-handling-test
  (testing "semicolon comments"
    (is (= 42 (eval* "42 ; this is a comment")))
    (is (= [1 2] (eval* "[1 ; comment\n2]")))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest reader-edge-cases-test
  (testing "empty input"
    ;; Empty input should return nil
    (is (nil? (eval* ""))))
  (testing "whitespace only" (is (nil? (eval* "   \n\t  "))))
  (testing "deeply nested structures"
    (is (= [[[[[1]]]]] (eval* "[[[[[1]]]]]")))))

(deftest special-float-values-test
  (testing "special float values"
    (is (Double/isInfinite (eval* "##Inf")))
    (is (Double/isInfinite (eval* "##-Inf")))
    (is (Double/isNaN (eval* "##NaN")))))
