;; klujur-std - Standard library macros
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

;; ============================================================================
;; Gensym Naming Convention
;; ============================================================================
;;
;; CONVENTION: All gensym calls MUST use an underscore suffix
;;
;; Examples:
;;   (gensym "x_")      - for binding names
;;   (gensym "case_")   - for macro-specific temporaries
;;   (gensym "args_")   - for argument lists
;;   (gensym (str var-name "_impl_"))  - for generated implementations
;;
;; RATIONALE:
;; - Consistent naming makes generated code more readable in macroexpansions
;; - Underscore suffix clearly indicates generated/temporary variables
;; - Follows Clojure convention (though Clojure uses # for auto-gensym)
;; - Makes debugging macro expansions easier

;; ============================================================================
;; Bootstrap aliases - these are redefined with full support later
;; ============================================================================

;; map*, filter*, remove*, take*, drop* are Rust builtins for 2-arity
;; These aliases allow macros to use them before full multi-arity versions
#_{:clj-kondo/ignore [:redefined-var :unresolved-symbol]}
(def map map*)
#_{:clj-kondo/ignore [:redefined-var :unresolved-symbol]}
(def filter filter*)
#_{:clj-kondo/ignore [:redefined-var :unresolved-symbol]}
(def remove remove*)
#_{:clj-kondo/ignore [:redefined-var :unresolved-symbol]}
(def take take*)
#_{:clj-kondo/ignore [:redefined-var :unresolved-symbol]}
(def drop drop*)

;; ============================================================================
;; Type Symbols for extend-type
;; ============================================================================

;; These symbols are used with extend-type to specify type implementations
(def Vector 'Vector)
(def List 'List)
(def Map 'Map)
(def Set 'Set)
(def String 'String)
(def Keyword 'Keyword)
(def Symbol 'Symbol)
(def Atom 'Atom)

;; ============================================================================
;; Function Definition Macros
;; ============================================================================

(defmacro defn
  "Same as (def name (fn [params*] exprs*)) or (def name (fn ([params*] exprs*)+))
   with any doc-string or attrs added to the var metadata."
  [name & fdecl]
  (let [;; Extract optional docstring
        m             (if (string? (first fdecl)) {:doc (first fdecl)} {})
        fdecl         (if (string? (first fdecl)) (rest fdecl) fdecl)
        ;; Extract optional attr-map before params
        m             (if (map? (first fdecl)) (merge m (first fdecl)) m)
        fdecl         (if (map? (first fdecl)) (rest fdecl) fdecl)
        ;; Normalise single-arity [params] body to ([params] body) form
        ;; but keep as vector+body for single-arity (fn expects that)
        single-arity? (vector? (first fdecl))
        ;; Extract arglists for metadata
        arglists      (if single-arity? (list (first fdecl)) (map first fdecl))
        m             (assoc m :arglists (list 'quote arglists))
        ;; Merge with any existing metadata on name
        m             (merge (meta name) m)]
    ;; Pass name to fn for self-recursion support
    `(def ~(with-meta name m) (fn ~name ~@fdecl))))

(defmacro defn-
  "Same as defn, yielding non-public def."
  [name & decls]
  (list* 'defn (with-meta name (assoc (meta name) :private true)) decls))

(defmacro defonce
  "defs name to have the root value of the expr iff the named var has no root value,
   else expr is unevaluated"
  [name expr]
  ;; Check if var exists and is bound (has a root value, even if nil)
  ;; This matches Clojure semantics where (defonce x nil) prevents
  ;; redefinition
  (let [v (gensym "v")]
    `(let [~v (resolve '~name)]
       (when (or (nil? ~v) (not (bound? ~v))) (def ~name ~expr)))))

(defmacro declare
  "defs the supplied var names with no bindings, useful for making forward declarations."
  [& names]
  (cons 'do (map (fn [n] (list 'def n)) names)))

(defmacro comment "Ignores body, yields nil" [& _body] nil)

(defmacro doto
  "Evaluates x then calls all of the methods and functions with the
   value of x supplied at the front of the given arguments. The forms
   are evaluated in order. Returns x."
  [x & forms]
  (let [gx    (gensym "x_")
        calls (map (fn [f]
                     (if (seq? f) (list* (first f) gx (next f)) (list f gx)))
                   forms)]
    (list 'let [gx x] (apply list 'do (concat calls (list gx))))))

(defmacro assert
  "Evaluates expr and throws an exception if it does not evaluate to
   logical true."
  ([x]
   `(when-not ~x
      (throw (ex-info (str "Assert failed: " '~x) {:type :assertion-error}))))
  ([x message]
   `(when-not ~x
      (throw (ex-info (str "Assert failed: " ~message)
                      {:type :assertion-error})))))

;; ============================================================================
;; Conditional Binding Macros
;; ============================================================================

(defn assert-binding-vec*
  "Validates that bind-vec is a 2-element vector. Throws helpful error if not.
   For internal use by binding macros."
  [macro-name bind-vec]
  (when-not (vector? bind-vec)
    (throw (ex-info (str macro-name
                         " requires a vector for its binding, got "
                         (type bind-vec))
                    {:type :syntax-error :macro macro-name})))
  (when-not (= 2 (count bind-vec))
    (throw (ex-info (str macro-name
                         " requires exactly 2 forms in binding vector, got "
                         (count bind-vec))
                    {:type :syntax-error :macro macro-name}))))

(defmacro if-let
  "Binds test to bind-vec, evaluates then if truthy, else otherwise."
  ([bind-vec then]
   `(if-let ~bind-vec
            ~then
            nil))
  ([bind-vec then else]
   (assert-binding-vec* "if-let" bind-vec)
   (let [form (bind-vec 0)
         tst  (bind-vec 1)]
     `(let [temp# ~tst]
        (if temp#
          (let [~form temp#]
            ~then)
          ~else)))))

(defmacro when-let
  "Binds test to bind-vec, evaluates body if truthy."
  [bind-vec & body]
  (assert-binding-vec* "when-let" bind-vec)
  (let [form (bind-vec 0)
        tst  (bind-vec 1)]
    `(let [temp# ~tst]
       (when temp#
         (let [~form temp#]
           ~@body)))))

(defmacro if-some
  "Binds test to bind-vec if non-nil (not falsy), evaluates then, else otherwise."
  ([bind-vec then]
   `(if-some ~bind-vec
             ~then
             nil))
  ([bind-vec then else]
   (assert-binding-vec* "if-some" bind-vec)
   (let [form (bind-vec 0)
         tst  (bind-vec 1)]
     `(let [temp# ~tst]
        (if (nil? temp#)
          ~else
          (let [~form temp#]
            ~then))))))

(defmacro when-some
  "Binds test to bind-vec if non-nil, evaluates body."
  [bind-vec & body]
  (assert-binding-vec* "when-some" bind-vec)
  (let [form (bind-vec 0)
        tst  (bind-vec 1)]
    `(let [temp# ~tst]
       (when (some? temp#)
         (let [~form temp#]
           ~@body)))))

(defmacro when-first
  "Binds first element of coll to bind-vec, evaluates body if coll non-empty."
  [bind-vec & body]
  (assert-binding-vec* "when-first" bind-vec)
  (let [form (bind-vec 0)
        coll (bind-vec 1)]
    `(when-let [s# (seq ~coll)]
       (let [~form (first s#)]
         ~@body))))

;; ============================================================================
;; Conditional Threading Macros
;; ============================================================================

(defmacro cond->
  "Takes an expression and a set of test/form pairs. Threads expr (via ->)
   through each form for which the corresponding test expression is true.
   Note that, unlike cond branching, cond-> threading does not short circuit
   after the first true test expression."
  [expr & clauses]
  (if (empty? clauses)
    expr
    (let [g     (gensym "cond->_")
          steps (vec (map (fn [[test step]]
                            `(if ~test
                               (-> ~g
                                   ~step)
                               ~g))
                          (partition 2 clauses)))]
      `(let [~g ~expr
             ~@(mapcat (fn [step] [g step]) (butlast steps))]
         ~(last steps)))))

(defmacro cond->>
  "Takes an expression and a set of test/form pairs. Threads expr (via ->>)
   through each form for which the corresponding test expression is true."
  [expr & clauses]
  (if (empty? clauses)
    expr
    (let [g     (gensym "cond->>_")
          steps (vec (map (fn [[test step]]
                            `(if ~test
                               (->> ~g
                                    ~step)
                               ~g))
                          (partition 2 clauses)))]
      `(let [~g ~expr
             ~@(mapcat (fn [step] [g step]) (butlast steps))]
         ~(last steps)))))

(defmacro some->
  "When expr is not nil, threads it into the first form (via ->),
   and when that result is not nil, through the next etc."
  [expr & forms]
  (let [g     (gensym "some->_")
        steps (vec (map (fn [step]
                          `(if (nil? ~g)
                             nil
                             (-> ~g
                                 ~step)))
                        forms))]
    `(let [~g ~expr
           ~@(mapcat (fn [step] [g step]) (butlast steps))]
       ~(if (empty? steps) g (last steps)))))

(defmacro some->>
  "When expr is not nil, threads it into the first form (via ->>),
   and when that result is not nil, through the next etc."
  [expr & forms]
  (let [g     (gensym "some->>_")
        steps (vec (map (fn [step]
                          `(if (nil? ~g)
                             nil
                             (->> ~g
                                  ~step)))
                        forms))]
    `(let [~g ~expr
           ~@(mapcat (fn [step] [g step]) (butlast steps))]
       ~(if (empty? steps) g (last steps)))))

;; ============================================================================
;; Case and Condp
;; ============================================================================

(defmacro case
  "Dispatch on constant values. Uses O(1) map lookup for efficient dispatch.

  (case x
    :a \"got a\"
    :b \"got b\"
    \"default\")

  Multiple values can be matched with a list:

  (case x
    (:a :b) \"got a or b\"
    :c \"got c\")"
  [expr & clauses]
  (let [default         (if (odd? (count clauses))
                          (last clauses)
                          `(throw (ex-info (str "No matching clause: " ~expr)
                                           {:value ~expr})))
        pairs           (vec
                         (if (odd? (count clauses)) (butlast clauses) clauses))
        g               (gensym "case_")
        ;; Build indexed result fns: {0 (fn [] result0), 1 (fn [] result1),
        ;; ...}
        ;; We use thunks to avoid evaluating all branches
        indexed-pairs   (vec (map-indexed vector (partition 2 pairs)))
        ;; Build the dispatch map: {test-val index, ...}
        ;; We build this manually to avoid lazy-seq issues with into. Only
        ;; symbols need quoting - numbers, keywords, strings are
        ;; self-evaluating
        quote-if-needed (fn [k] (if (symbol? k) (list 'quote k) k))
        dispatch-map    (reduce (fn [m [idx [test _then]]]
                                  (if (list? test)
                                    ;; Multiple values map to same index
                                    (reduce
                                     (fn [m2 t]
                                       (assoc m2 (quote-if-needed t) idx))
                                     m
                                     test)
                                    (assoc m (quote-if-needed test) idx)))
                                {}
                                indexed-pairs)
        ;; Build thunks for each branch
        thunks          (vec (map (fn [[_idx [_test then]]] `(fn [] ~then))
                                  indexed-pairs))
        thunks-sym      (gensym "thunks_")]
    `(let [~g ~expr
           ~thunks-sym ~thunks]
       (if-let [idx# (get ~dispatch-map ~g)]
         ((nth ~thunks-sym idx#))
         ~default))))

(defmacro condp
  "Dispatch on predicate results."
  [pred expr & clauses]
  (let [g    (gensym "condp_")
        emit (fn emit [clauses]
               (if (empty? clauses)
                 `(throw (ex-info (str "No matching clause") {:value ~g}))
                 (let [c  (first clauses)
                       cs (next clauses)]
                   (if (nil? cs)
                     ;; Default clause (odd number of forms)
                     c
                     (if (= (first cs) :>>)
                       ;; :>> threading form: test-expr :>> result-fn
                       (let [result-fn (second cs)]
                         `(if-let [result# (~pred ~c ~g)]
                            (~result-fn result#)
                            ~(emit (nnext cs))))
                       ;; Normal clause: test-expr result-expr
                       `(if (~pred ~c ~g) ~(first cs) ~(emit (rest cs))))))))]
    `(let [~g ~expr]
       ~(emit clauses))))

;; ============================================================================
;; Iteration Macros
;; ============================================================================

(defmacro dotimes
  "Execute body n times with bind-vec bound to 0..n-1."
  [bind-vec & body]
  (let [i (bind-vec 0)
        n (bind-vec 1)]
    `(let [n# ~n]
       (loop [~i 0]
         (when (< ~i n#) ~@body (recur (inc ~i)))))))

(defmacro while
  "Repeatedly execute body while test is truthy."
  [test & body]
  `(loop []
     (when ~test ~@body (recur))))

(defmacro doseq
  "Iterate over sequence(s), executing body for side effects."
  [bindings & body]
  (if (empty? bindings)
    `(do ~@body nil)
    (let [b  (first bindings)
          bs (rest bindings)]
      (if (keyword? b)
        ;; Handle :when, :let, :while modifiers
        (cond (= b :when) `(when ~(first bs)
                             (doseq ~(rest bs)
                                    ~@body))
              (= b :let) `(let ~(first bs)
                               (doseq ~(rest bs)
                                      ~@body))
              ;; :while returns ::doseq-stop sentinel to terminate outer
              ;; loop (namespaced to avoid collision with user keywords)
              (= b :while) `(if ~(first bs)
                              (doseq ~(rest bs)
                                     ~@body)
                              ::doseq-stop)
              :else `(doseq ~(rest bs)
                            ~@body))
        ;; Sequence binding - check for ::doseq-stop to terminate early
        (let [sym  (first bindings)
              expr (second bindings)
              more (drop 2 bindings)]
          `(loop [s# (seq ~expr)]
             (when s#
               (let [result# (let [~sym (first s#)]
                               (doseq ~(vec more)
                                      ~@body))]
                 (when-not (= result# ::doseq-stop) (recur (next s#)))))))))))

;; NOTE: These helper functions for the `for` macro MUST remain public.
;;
;; DECISION: Cannot make these private (blocked in TODO.md)
;;
;; REASON: The `for` macro uses syntax-quote which qualifies symbols as
;; klujur.core/for-step. When a user calls (for ...) from the 'user namespace,
;; the macro expands and generates code that references klujur.core/for-step.
;; That generated code executes in the 'user namespace context.
;;
;; In Klujur, private vars can only be accessed from within the same namespace
;; (see eval/mod.rs lines 216 and 231: `if !var.is_public() && var_ns !=
;; current_ns_name`).
;; Since the generated code runs in a different namespace than klujur.core,
;; making these functions private would cause "var: klujur.core/for-step is not
;; public" errors.
;;
;; ALTERNATIVES CONSIDERED:
;; 1. Unqualified references - doesn't work, syntax-quote always qualifies
;; 2. Inline expansion - would make macro too complex and hurt performance
;; 3. Same-namespace access exception - would require runtime changes
;;
;; CONCLUSION: These must remain public as part of klujur.core's API.
(defn for-step
  "Helper for the for macro - iterates over seq, applying f to each element.
   Stops early if f returns a result containing [::for-while-stop]."
  [f s]
  (lazy-seq (when s
              (let [result (f (first s))]
                (if (and (vector? result) (= (first result) ::for-while-stop))
                  nil ;; :while terminated - stop iteration
                  (concat result (for-step f (next s))))))))

(defn for-emit
  "Helper for the for macro - emits code for bindings."
  [bindings body-expr]
  (if (empty? bindings)
    ;; Base case: emit the body wrapped in list
    `(list ~body-expr)
    (let [b  (first bindings)
          bs (rest bindings)]
      (if (keyword? b)
        ;; Handle modifiers
        (cond (= b :when) `(if ~(first bs) ~(for-emit (rest bs) body-expr) ())
              (= b :let) `(let ~(first bs)
                               ~(for-emit (rest bs) body-expr))
              ;; :while terminates iteration when false (uses
              ;; ::for-while-stop sentinel - namespace-qualified for
              ;; safety)
              (= b :while) `(if ~(first bs)
                              ~(for-emit (rest bs) body-expr)
                              [::for-while-stop])
              :else (for-emit (rest bs) body-expr))
        ;; Sequence binding - use for-step to handle :while termination
        (let [sym  (first bindings)
              expr (second bindings)
              more (drop 2 bindings)]
          `(for-step (fn [~sym] ~(for-emit (vec more) body-expr))
                     (seq ~expr)))))))

(defmacro for
  "List comprehension. Takes a vector of one or more binding-form/collection-expr
   pairs, each followed by zero or more modifiers, and yields a lazy sequence of
   evaluations of expr.

   Supported modifiers:
     :when test - only include results where test is truthy
     :let bindings - introduce local bindings
     :while test - continue while test is truthy, then stop"
  [bindings body-expr]
  `(lazy-seq ~(for-emit bindings body-expr)))

;; ============================================================================
;; Local Functions
;; ============================================================================

(defmacro letfn
  "Bind local functions that can reference each other.

   Uses volatiles to enable mutual recursion - each function can call
   the others even though they're defined simultaneously.

   Example:
     (letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
             (odd? [n] (if (zero? n) false (even? (dec n))))]
       (even? 10))  ; => true

   Note: This implementation introduces an extra layer of indirection
   via wrapper functions. For performance-critical code with deep
   recursion, consider using a single recursive function with a
   dispatch parameter instead."
  [fnspecs & body]
  (let [names            (vec (map first fnspecs))
        ;; Create gensyms for the volatile references
        vol-syms         (vec (map (fn [n] (gensym (str n "_vol_"))) names))
        ;; Bindings that create volatiles initialized to nil
        vol-bindings     (vec (mapcat (fn [v] [v (list 'volatile! nil)])
                               vol-syms))
        ;; Map from name to its volatile symbol
        name->vol        (zipmap names vol-syms)
        ;; Create wrapper functions that deref their volatiles
        wrapper-bindings (vec (mapcat (fn [[name vol]]
                                        (let [args-sym (gensym "args_")]
                                          [name
                                           (list 'fn
                                                 (vector '& args-sym)
                                                 (list 'apply
                                                       (list 'deref vol)
                                                       args-sym))]))
                               name->vol))
        ;; Create the actual function implementations
        impl-syms        (vec (map (fn [n] (gensym (str n "_impl_"))) names))
        impl-bindings    (vec (mapcat (fn [spec impl-sym] [impl-sym
                                                           (list* 'fn
                                                                  (rest spec))])
                               fnspecs
                               impl-syms))
        ;; Set the volatiles to the implementations
        set-exprs        (vec (map (fn [vol impl] (list 'vreset! vol impl))
                                   vol-syms
                                   impl-syms))
        all-bindings     (vec
                          (concat vol-bindings wrapper-bindings impl-bindings))]
    (list* 'let all-bindings (concat set-exprs body))))

;; ============================================================================
;; Lazy Sequence Macros
;; ============================================================================

(defmacro lazy-cat
  "Expands to code that yields a lazy sequence of the concatenation
   of the supplied colls. Each coll expr is not evaluated until it is
   needed."
  [& colls]
  (apply list 'concat (map (fn [coll] (list 'lazy-seq coll)) colls)))

;; ============================================================================
;; Lazy Sequence Functions
;; ============================================================================

(defn iterate
  "Returns a lazy sequence of x, (f x), (f (f x)) etc."
  [f x]
  (lazy-seq (cons x (iterate f (f x)))))

(defn cycle
  "Returns a lazy (infinite!) sequence of repetitions of the items in coll."
  [coll]
  (lazy-seq (when-let [s (seq coll)]
              (concat s (cycle s)))))

(defn repeatedly
  "Takes a function of no args, presumably with side effects, and returns
   an infinite (or length n if supplied) lazy sequence of calls to it."
  ([f] (lazy-seq (cons (f) (repeatedly f))))
  ([n f] (lazy-seq (when (pos? n) (cons (f) (repeatedly (dec n) f))))))

;; ============================================================================
;; Core Lazy Sequence Transformations
;; ============================================================================

(defn map
  "Returns a lazy sequence consisting of the result of applying f to
   the set of first items of each coll, followed by applying f to the
   set of second items in each coll, until any one of the colls is
   exhausted. Any remaining items in other colls are ignored.
   When called with 1 arg (f), returns a transducer."
  ([f]
   (fn [rf]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input] (rf result (f input))))))
  ([f coll]
   (lazy-seq (when-let [s (seq coll)]
               (if (chunked-seq? s)
                 (let [c    (chunk-first s)
                       size (chunk-count c)
                       b    (chunk-buffer size)]
                   (dotimes [i size]
                     (chunk-append b (f (chunk-nth c i))))
                   (chunk-cons (chunk b) (map f (chunk-rest s))))
                 (cons (f (first s)) (map f (rest s)))))))
  ([f c1 c2]
   (lazy-seq (let [s1 (seq c1)
                   s2 (seq c2)]
               (when (and s1 s2)
                 (cons (f (first s1) (first s2))
                       (map f (rest s1) (rest s2)))))))
  ([f c1 c2 c3]
   (lazy-seq (let [s1 (seq c1)
                   s2 (seq c2)
                   s3 (seq c3)]
               (when (and s1 s2 s3)
                 (cons (f (first s1) (first s2) (first s3))
                       (map f (rest s1) (rest s2) (rest s3)))))))
  ([f c1 c2 c3 & colls]
   (let [step (fn step [cs]
                (lazy-seq (let [ss (map seq cs)]
                            (when (every? identity ss)
                              (cons (map first ss) (step (map rest ss)))))))]
     (map #(apply f %) (step (cons c1 (cons c2 (cons c3 colls))))))))

(defn filter
  "Returns a lazy sequence of the items in coll for which
   (pred item) returns logical true.
   When called with 1 arg (pred), returns a transducer."
  ([pred]
   (fn [rf]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input] (if (pred input) (rf result input) result)))))
  ([pred coll]
   (lazy-seq (when-let [s (seq coll)]
               (if (chunked-seq? s)
                 (let [c    (chunk-first s)
                       size (chunk-count c)
                       b    (chunk-buffer size)]
                   (dotimes [i size]
                     (let [v (chunk-nth c i)]
                       (when (pred v) (chunk-append b v))))
                   (chunk-cons (chunk b) (filter pred (chunk-rest s))))
                 (let [f (first s)]
                   (if (pred f)
                     (cons f (filter pred (rest s)))
                     (filter pred (rest s)))))))))

(defn remove
  "Returns a lazy sequence of the items in coll for which
   (pred item) returns logical false.
   When called with 1 arg (pred), returns a transducer."
  ([pred] (filter (complement pred)))
  ([pred coll] (filter (complement pred) coll)))

(defn concat
  "Returns a lazy seq representing the concatenation of the elements
   in the supplied colls."
  ([] (lazy-seq nil))
  ([x] (lazy-seq x))
  ([x y]
   (lazy-seq (let [s (seq x)]
               (if s (cons (first s) (concat (rest s) y)) y))))
  ([x y & zs] (lazy-cat (concat x y) (apply concat zs))))

(defn range
  "Returns a lazy seq of nums from start (inclusive) to end (exclusive),
   by step, where start defaults to 0, step to 1, and end to infinity.
   For finite ranges (1-3 args), returns an eager list for better performance.
   For infinite range (no args), returns a lazy sequence."
  ([] (iterate inc 0))
  ([end] (range-builtin end))
  ([start end] (range-builtin start end))
  ([start end step] (range-builtin start end step)))

(defn repeat
  "Returns a lazy (infinite!, or length n if supplied) sequence of xs."
  ([x] (lazy-seq (cons x (repeat x))))
  ([n x] (lazy-seq (when (pos? n) (cons x (repeat (dec n) x))))))

;; ============================================================================
;; Take/Drop Functions
;; ============================================================================

(defn take
  "Returns a lazy sequence of the first n items in coll, or all items if
   there are fewer than n. Returns a stateful transducer when called with 1 arg."
  ([n]
   (fn [rf]
     (let [nv (volatile! n)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [n      @nv
                nn     (vswap! nv dec)
                result (if (pos? n) (rf result input) result)]
            (if (not (pos? nn)) (ensure-reduced result) result)))))))
  ([n coll] (take* n coll)))

(defn drop
  "Returns a lazy sequence of all but the first n items in coll.
   Returns a stateful transducer when called with 1 arg."
  ([n]
   (fn [rf]
     (let [nv (volatile! n)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [n @nv]
            (vswap! nv dec)
            (if (pos? n) result (rf result input))))))))
  ([n coll] (drop* n coll)))

;; ============================================================================
;; Conditional Take/Drop Functions
;; ============================================================================

(defn take-while
  "Returns a lazy sequence of successive items from coll while
   (pred item) returns logical true.
   When called with 1 arg (pred), returns a transducer."
  ([pred]
   (fn [rf]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input] (if (pred input) (rf result input) (reduced result))))))
  ([pred coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [f (first s)]
                 (when (pred f) (cons f (take-while pred (rest s)))))))))

(defn drop-while
  "Returns a lazy sequence of the items in coll starting from the
   first item for which (pred item) returns logical false.
   When called with 1 arg (pred), returns a transducer."
  ([pred]
   (fn [rf]
     (let [done (volatile! false)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (if @done
            (rf result input)
            (if (pred input)
              result
              (do (vreset! done true) (rf result input)))))))))
  ([pred coll]
   (lazy-seq (let [s (seq coll)]
               (if (and s (pred (first s))) (drop-while pred (rest s)) s)))))

(defn take-nth
  "Returns a lazy seq of every nth item in coll.
   When called with 1 arg (n), returns a transducer."
  ([n]
   (fn [rf]
     (let [iv (volatile! -1)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [i (vswap! iv inc)]
            (if (zero? (rem i n)) (rf result input) result)))))))
  ([n coll]
   (lazy-seq (when-let [s (seq coll)]
               (cons (first s) (take-nth n (drop n s)))))))

(defn take-last
  "Returns a seq of the last n items in coll. Necessarily realises coll."
  [n coll]
  (loop [s    (seq coll)
         lead (seq (drop n coll))]
    (if lead (recur (next s) (next lead)) s)))

(defn drop-last
  "Return a lazy sequence of all but the last n (default 1) items in coll."
  ([coll] (drop-last 1 coll))
  ([n coll]
   (lazy-seq (let [s (seq coll)]
               (when (seq (drop n s))
                 (cons (first s) (drop-last n (rest s))))))))

;; ============================================================================
;; Split Functions
;; ============================================================================

(defn split-at
  "Returns a vector of [(take n coll) (drop n coll)]."
  [n coll]
  [(take n coll) (drop n coll)])

(defn split-with
  "Returns a vector of [(take-while pred coll) (drop-while pred coll)]."
  [pred coll]
  [(take-while pred coll) (drop-while pred coll)])

;; ============================================================================
;; Partition Functions
;; ============================================================================

(defn partition
  "Returns a lazy sequence of lists of n items each, at offsets step apart.
   If step is not supplied, defaults to n. If a pad collection is supplied,
   use its elements to complete the last partition if needed."
  ([n coll] (partition n n coll))
  ([n step coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [p (doall (take n s))]
                 (when (= n (count p))
                   (cons p (partition n step (drop step s))))))))
  ([n step pad coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [p (doall (take n s))]
                 (if (= n (count p))
                   (cons p (partition n step pad (drop step s)))
                   (list (doall (take n (concat p pad))))))))))

;; ============================================================================
;; Interleaving Functions
;; ============================================================================

(defn interleave
  "Returns a lazy seq of the first item in each coll, then the second etc."
  ([c1 c2]
   (lazy-seq (let [s1 (seq c1)
                   s2 (seq c2)]
               (when (and s1 s2)
                 (cons (first s1)
                       (cons (first s2) (interleave (rest s1) (rest s2))))))))
  ([c1 c2 & colls]
   (lazy-seq (let [ss (map seq (cons c1 (cons c2 colls)))]
               (when (every? identity ss)
                 (concat (map first ss) (apply interleave (map rest ss))))))))

(defn interpose
  "Returns a lazy seq of the elements of coll separated by sep.
   When called with 1 arg (sep), returns a transducer."
  ([sep]
   (fn [rf]
     (let [started (volatile! false)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (if @started
            (let [sepr (rf result sep)]
              (if (reduced? sepr) sepr (rf sepr input)))
            (do (vreset! started true) (rf result input))))))))
  ([sep coll]
   (lazy-seq (when-let [s (seq coll)]
               (cons (first s) (mapcat (fn [x] [sep x]) (rest s)))))))

;; ============================================================================
;; Mapping Variants
;; ============================================================================

(defn mapcat
  "Returns the result of applying concat to the result of applying map
   to f and colls. Thus function f should return a collection.
   When called with 1 arg (f), returns a transducer."
  ([f]
   (comp (map f)
         (cat)))
  ([f coll] (apply concat (map f coll)))
  ([f & colls] (apply concat (apply map f colls))))

(defn map-indexed
  "Returns a lazy sequence consisting of the result of applying f to 0
   and the first item of coll, followed by applying f to 1 and the second
   item in coll, etc.
   When called with 1 arg (f), returns a transducer."
  ([f]
   (fn [rf]
     (let [iv (volatile! -1)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [i (vswap! iv inc)]
            (rf result (f i input))))))))
  ([f coll]
   (letfn [(step [idx s]
             (lazy-seq (when-let [s (seq s)]
                         (cons (f idx (first s)) (step (inc idx) (rest s))))))]
     (step 0 coll))))

;; ============================================================================
;; Keep Functions
;; ============================================================================

(defn keep
  "Returns a lazy sequence of the non-nil results of (f item).
   When called with 1 arg (f), returns a transducer."
  ([f]
   (fn [rf]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input]
        (let [v (f input)]
          (if (nil? v) result (rf result v)))))))
  ([f coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [x (f (first s))]
                 (if (nil? x) (keep f (rest s)) (cons x (keep f (rest s)))))))))

(defn keep-indexed
  "Returns a lazy sequence of the non-nil results of (f index item).
   When called with 1 arg (f), returns a transducer."
  ([f]
   (fn [rf]
     (let [iv (volatile! -1)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [i (vswap! iv inc)
                v (f i input)]
            (if (nil? v) result (rf result v))))))))
  ([f coll]
   (letfn [(step [idx s]
             (lazy-seq (when-let [s (seq s)]
                         (let [x (f idx (first s))]
                           (if (nil? x)
                             (step (inc idx) (rest s))
                             (cons x (step (inc idx) (rest s))))))))]
     (step 0 coll))))

;; ============================================================================
;; Misc Sequence Functions
;; ============================================================================

(defn flatten
  "Takes any nested combination of sequential things and returns their
   contents as a single, flat lazy sequence."
  [x]
  (lazy-seq (cond (nil? x) nil
                  (sequential? x) (when-let [s (seq x)]
                                    (concat (flatten (first s))
                                            (flatten (rest s))))
                  :else (list x))))

(defn reductions
  "Returns a lazy seq of the intermediate values of the reduction of
   coll by f, starting with init."
  ([f coll]
   (lazy-seq (when-let [s (seq coll)]
               (reductions f (first s) (rest s)))))
  ([f init coll]
   (lazy-seq (cons init
                   (when-let [s (seq coll)]
                     (reductions f (f init (first s)) (rest s)))))))

;; ============================================================================
;; Eager Variants
;; ============================================================================

(defn mapv
  "Returns a vector consisting of the result of applying f to the
   set of first items of each coll, followed by applying f to the set
   of second items in each coll, until any one of the colls is exhausted."
  ([f coll] (vec (map f coll)))
  ([f c1 c2] (vec (map f c1 c2)))
  ([f c1 c2 c3] (vec (map f c1 c2 c3)))
  ([f c1 c2 c3 & colls] (vec (apply map f c1 c2 c3 colls))))

(defn filterv
  "Returns a vector of the items in coll for which
   (pred item) returns logical true."
  [pred coll]
  (reduce (fn [v x] (if (pred x) (conj v x) v)) [] coll))

;; ============================================================================
;; Transducer-producing Functions (no lazy seq equivalent)
;; ============================================================================

(defn preserving-reduced
  "Wraps a reducing function to preserve reduced status through nested reductions.
   Used by cat and mapcat to properly propagate early termination."
  [rf]
  (fn [acc input]
    (let [result (rf acc input)]
      (if (reduced? result) (reduced result) result))))

(defn cat
  "A transducer which concatenates nested collections.
   Can be used directly (cat) or called with no args ((cat))."
  ([] cat) ;; 0-arity returns cat itself for backward compatibility
  ([rf]
   (let [rrf (preserving-reduced rf)]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input] (reduce rrf result input))))))

(defn dedupe
  "Returns a lazy sequence removing consecutive duplicates.
   When called with no args, returns a transducer."
  ([]
   (fn [rf]
     (let [pv (volatile! ::none)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (let [prior @pv]
            (vreset! pv input)
            (if (= prior input) result (rf result input))))))))
  ([coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [f (first s)]
                 (cons f (dedupe (drop-while #(= f %) (rest s)))))))))

(defn distinct
  "Returns a lazy sequence of the elements of coll with duplicates removed.
   When called with no args, returns a transducer."
  ([]
   (fn [rf]
     (let [seen (volatile! #{})]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result input]
          (if (contains? @seen input)
            result
            (do (vswap! seen conj input) (rf result input))))))))
  ([coll]
   (lazy-seq (letfn [(step [s seen]
                       (lazy-seq
                        (when-let [s (seq s)]
                          (let [f (first s)]
                            (if (contains? seen f)
                              (step (rest s) seen)
                              (cons f (step (rest s) (conj seen f))))))))]
               (step coll #{})))))

(defn partition-all
  "Returns a lazy sequence of partitions, each of n items.
   May include a partition with fewer than n items at the end.
   When called with 1 arg (n), returns a transducer."
  ([n]
   (fn [rf]
     (let [a (volatile! [])]
       (fn
         ([] (rf))
         ([result]
          (let [result (if (empty? @a)
                         result
                         (let [v @a]
                           (vreset! a [])
                           (unreduced (rf result v))))]
            (rf result)))
         ([result input]
          (let [v (vswap! a conj input)]
            (if (= n (count v)) (do (vreset! a []) (rf result v)) result)))))))
  ([n coll] (partition-all n n coll))
  ([n step coll]
   (lazy-seq (when-let [s (seq coll)]
               (cons (doall (take n s))
                     (partition-all n step (drop step s)))))))

(defn partition-by
  "Applies f to each value in coll, splitting when f returns a new value.
   When called with 1 arg (f), returns a transducer."
  ([f]
   (fn [rf]
     (let [a  (volatile! [])
           pv (volatile! ::none)]
       (fn
         ([] (rf))
         ([result]
          (let [result (if (empty? @a)
                         result
                         (let [v @a]
                           (vreset! a [])
                           (unreduced (rf result v))))]
            (rf result)))
         ([result input]
          (let [pval @pv
                val  (f input)]
            (vreset! pv val)
            (if (or (= pval ::none) (= val pval))
              (do (vswap! a conj input) result)
              (let [v @a]
                (vreset! a [input])
                (rf result v)))))))))
  ([f coll]
   (lazy-seq (when-let [s (seq coll)]
               (let [fst (first s)
                     fv  (f fst)
                     run (cons fst (take-while #(= fv (f %)) (rest s)))]
                 (cons run (partition-by f (drop (count run) s))))))))

;; ============================================================================
;; Namespace Macro
;; ============================================================================

(defmacro ns
  "Sets *ns* to the namespace named by name (creating it if needed), and
   optionally processes require/use clauses.

   Clauses:
     (:require [lib :as alias] [lib :refer [names...]])
     (:use [lib :only [names...] :exclude [names...] :rename {from to}])
     (:refer-klujur :exclude [names...])

   Example:
     (ns my.app.core
       (:require [mylib.utils :as u]
                 [mylib.core :refer [main]]))"
  [name & clauses]
  (let [process-clause (fn [clause]
                         (let [type  (first clause)
                               specs (rest clause)]
                           (cond (= type :require)
                                 (map (fn [spec]
                                        (list 'require (list 'quote spec)))
                                      specs)
                                 (= type :use)
                                 (map (fn [spec] (list 'use (list 'quote spec)))
                                      specs)
                                 (= type :refer-klujur)
                                 (list (apply list
                                              'refer
                                              (list 'quote 'klujur.core)
                                              specs))
                                 :else nil)))
        all-forms      (vec (mapcat process-clause clauses))]
    (apply list 'do (list 'in-ns (list 'quote name)) all-forms)))

;; ============================================================================
;; Transducers
;; ============================================================================

(defn completing
  "Takes a reducing function f of 2 args and returns a fn suitable for
   transduce by adding arity-1 as identity and arity-0 as (f)."
  ([f] (completing f identity))
  ([f cf]
   (fn ([] (f)) ([result] (cf result)) ([result input] (f result input)))))


;; ============================================================================
;; Sequence with Transducer
;; ============================================================================

(defn sequence
  "Coerces coll to a (possibly lazy) sequence. If coll is already a sequence,
   returns it. If coll is empty, returns ().

   When a transducer is supplied, returns a lazy sequence of applications of
   the transform to the items in coll(s). The transform should accept the
   number of items provided in the colls."
  ([coll] (or (seq coll) '()))
  ([xform coll]
   ;; Implementation using a multi-step approach: We use a volatile to
   ;; buffer items since transducers push while lazy-seqs pull. We step
   ;; through one input at a time, collecting any outputs, then yield them.
   ;; We track a result value (a vector) that gets passed to completion.
   (let [buffer (volatile! [])
         ;; Reducing function that collects items into buffer. The result
         ;; value is passed through unchanged; actual items go to buffer
         rf     (fn
                  ([] [])
                  ([result] result)
                  ([result item] (vswap! buffer conj item) result))
         ;; Apply the transducer to get the transforming rf
         xf     (xform rf)]
     (letfn
       [(step [s acc]
          (lazy-seq
           (if (seq s)
             ;; Step one input element through the transducer
             (let [result (xf acc (first s))]
               (if (reduced? result)
                 ;; Early termination - drain buffer and stop
                 (let [items     @buffer
                       unwrapped (unreduced result)]
                   (vreset! buffer [])
                   (xf unwrapped) ;; completion with unwrapped result
                   (let [final-items @buffer]
                     (vreset! buffer [])
                     (when (seq (concat items final-items))
                       (concat items final-items))))
                 ;; Normal case - drain buffer and continue
                 (let [items @buffer]
                   (vreset! buffer [])
                   (if (seq items)
                     (concat items (step (rest s) result))
                     (step (rest s) result)))))
             ;; Input exhausted - call completion and drain final items
             (do (xf acc) ;; completion with accumulated result
                 (let [items @buffer]
                   (vreset! buffer [])
                   (when (seq items) items))))))]
       (step (seq coll) (xf))))))

(defn eduction
  "Returns a reducible/iterable application of the transducers to the items
   in coll. Transducers are applied in order as if combined with comp.
   Note that these applications will be performed every time reduce/into/seq
   is called - eduction does not cache results like sequence does.

   Unlike sequence, eduction is not lazy - it represents a recipe for
   transformation that gets applied fresh each time it's consumed.

   DEVIATION FROM CLOJURE: In Clojure, eduction returns an Eduction object
   implementing IReduceInit, which allows direct participation in reduce/into.
   In Klujur, eduction returns a map with :xform and :coll keys. Use
   eduction-reduce to reduce an eduction, or eduction-seq to convert to a
   lazy sequence. Example:
     (def ed (eduction (map inc) (filter even?) [1 2 3 4]))
     (eduction-reduce ed conj [])  ; => [2 4]
     (eduction-seq ed)             ; => (2 4)"
  [& xforms-and-coll]
  (let [xforms (butlast xforms-and-coll)
        coll   (last xforms-and-coll)
        xform  (if (= 1 (count xforms)) (first xforms) (apply comp xforms))]
    ;; Return a map-like structure that can be:
    ;; - Reduced with (eduction-reduce ed f init)
    ;; - Converted to seq with (eduction-seq ed)
    (with-meta {:klujur/type :eduction :xform xform :coll coll}
               {:type :klujur.core/Eduction})))

(defn eduction?
  "Returns true if x is an eduction."
  [x]
  (= :eduction (:klujur/type x)))

(defn eduction-seq
  "Converts an eduction to a lazy sequence."
  [ed]
  (sequence (:xform ed) (:coll ed)))

(defn eduction-reduce
  "Reduces an eduction with the given function and initial value."
  ([ed f] (transduce (:xform ed) f (:coll ed)))
  ([ed f init] (transduce (:xform ed) f init (:coll ed))))

;; Shadow the builtin reduce to support eductions
(def reduce-builtin reduce)

(defn reduce
  "Reduces coll with f. If coll is an eduction, uses transduce internally."
  ([f coll]
   (if (eduction? coll) (eduction-reduce coll f) (reduce-builtin f coll)))
  ([f init coll]
   (if (eduction? coll)
     (eduction-reduce coll f init)
     (reduce-builtin f init coll))))

;; Shadow the builtin into to support eductions
(def into-builtin into)

(defn into
  "Returns a new coll of to-coll with items from coll conj'd.
   If coll is an eduction, uses transduce internally."
  ([to] to)
  ([to from]
   (if (eduction? from)
     (transduce (:xform from) conj to (:coll from))
     (into-builtin to from)))
  ([to xform from] (into-builtin to xform from)))

;; ============================================================================
;; Protocol Support
;; ============================================================================

(defmacro extend-protocol
  "Extend a protocol to multiple types at once.

   Usage:
   (extend-protocol MyProtocol
     String
     (method1 [s] (str \"Hello, \" s))
     (method2 [s x] (str s x))

     Vector
     (method1 [v] (str \"Vector: \" v))
     (method2 [v x] (conj v x)))

   Expands to multiple extend-type forms."
  [protocol & specs]
  (let [parse-specs (fn parse-specs [specs]
                      (loop [remaining specs
                             result    []]
                        (if (empty? remaining)
                          result
                          (let [type-sym   (first remaining)
                                ;; Collect method impls until next symbol
                                ;; (type) or end
                                methods    (take-while list? (rest remaining))
                                rest-specs (drop (inc (count methods))
                                                 remaining)]
                            (recur rest-specs
                                   (conj result
                                         `(extend-type ~type-sym
                                           ~protocol
                                           ~@methods)))))))]
    `(do ~@(parse-specs specs))))

;; ============================================================================
;; Core Protocols
;; ============================================================================
;; These protocols define the fundamental abstractions for sequences,
;; collections, and other core operations. They allow user-defined types
;; to participate in the seq abstraction.

(defprotocol ISeqable
  "Protocol for types that can be converted to a sequence."
  (-seq [coll]
   "Returns a seq on the collection, or nil if empty."))

(defprotocol ISeq
  "Protocol for sequence types that support first/rest decomposition."
  (-first [coll]
   "Returns the first element of the collection.")
  (-rest [coll]
   "Returns a seq of the rest of the collection."))

(defprotocol INext
  "Protocol for sequences that support efficient next operation."
  (-next [coll]
   "Returns the next seq, or nil if empty."))

(defprotocol ICollection
  "Protocol for general collection operations."
  (-count [coll]
   "Returns the number of items in the collection.")
  (-conj [coll x]
   "Returns a new collection with x added.")
  (-empty [coll]
   "Returns an empty collection of the same type."))

(defprotocol IAssociative
  "Protocol for associative data structures (maps, vectors)."
  (-assoc [coll k v]
   "Returns a new collection with key k associated to value v.")
  (-contains-key? [coll k]
   "Returns true if the collection contains key k."))

(defprotocol ILookup
  "Protocol for key-based lookup."
  (-lookup [coll k]
           [coll k not-found]
   "Returns the value at key k, or not-found/nil."))

(defprotocol IIndexed
  "Protocol for indexed access."
  (-nth [coll n]
        [coll n not-found]
   "Returns the value at index n, or not-found/error."))

(defprotocol IFn
  "Protocol for callable objects."
  (-invoke [f]
           [f a]
           [f a b]
           [f a b c]
           [f a b c d]
           [f a b c d & more]
   "Invokes the function with the given arguments."))

(defprotocol IDeref
  "Protocol for dereferenceable types."
  (-deref [ref]
   "Returns the current value of the reference."))

(defprotocol IMeta
  "Protocol for types that support metadata."
  (-meta [obj]
   "Returns the metadata map for the object."))

(defprotocol IWithMeta
  "Protocol for types that can have metadata attached."
  (-with-meta [obj m]
   "Returns a copy of obj with metadata m attached."))

(defn vary-meta
  "Returns an object of the same type and value as obj, with
   (apply f (meta obj) args) as its metadata."
  [obj f & args]
  (with-meta obj (apply f (meta obj) args)))

;; alter-meta! is now a special form in the evaluator, allowing it to be
;; used as a higher-order function (unlike the previous macro implementation)

(defprotocol ICounted
  "Protocol for types with O(1) count."
  (-counted? [coll]
   "Returns true if count is O(1)."))

(defprotocol IReduce
  "Protocol for reducible collections."
  (-reduce [coll f]
           [coll f init]
   "Reduces the collection using f."))

;; ============================================================================
;; Core Protocol Implementations for Built-in Types
;; ============================================================================
;; Note: These extend the core protocols to all built-in types.
;; The -prefixed methods are the protocol implementations, while
;; the unprefixed versions (seq, first, rest, etc.) remain as the
;; public API and will dispatch through the protocols.
;;
;; The implementations use the existing Rust builtins directly (first, rest,
;; count, etc.) since these are the native implementations. The protocol
;; methods provide the abstraction layer for user-defined types.

;; ISeqable implementations
(extend-type nil
 ISeqable
   (-seq [_] nil))

(extend-type List
 ISeqable
   (-seq [coll] (if (empty? coll) nil coll)))

(extend-type Vector
 ISeqable
   (-seq [coll] (if (empty? coll) nil (seq coll))))

(extend-type Map
 ISeqable
   (-seq [coll] (if (empty? coll) nil (seq coll))))

(extend-type Set
 ISeqable
   (-seq [coll] (if (empty? coll) nil (seq coll))))

(extend-type String
 ISeqable
   (-seq [s] (if (= "" s) nil (seq s))))

(extend-type LazySeq
 ISeqable
   (-seq [coll] (if (empty? coll) nil coll)))

;; ISeq implementations
(extend-type nil
 ISeq
   (-first [_] nil)
   (-rest [_] ()))

(extend-type List
 ISeq
   (-first [coll] (first coll))
   (-rest [coll] (rest coll)))

(extend-type LazySeq
 ISeq
   (-first [coll] (first coll))
   (-rest [coll] (rest coll)))

;; INext implementations
(extend-type nil
 INext
   (-next [_] nil))
(extend-type List
 INext
   (-next [coll] (next coll)))
(extend-type LazySeq
 INext
   (-next [coll] (next coll)))

;; ICollection implementations
(extend-type nil
 ICollection
   (-count [_] 0)
   (-conj [_ x] (list x))
   (-empty [_] nil))

(extend-type List
 ICollection
   (-count [coll] (count coll))
   (-conj [coll x] (conj coll x))
   (-empty [_] ()))

(extend-type Vector
 ICollection
   (-count [coll] (count coll))
   (-conj [coll x] (conj coll x))
   (-empty [_] []))

(extend-type Map
 ICollection
   (-count [coll] (count coll))
   (-conj [coll x] (conj coll x))
   (-empty [_] {}))

(extend-type Set
 ICollection
   (-count [coll] (count coll))
   (-conj [coll x] (conj coll x))
   (-empty [_] #{}))

;; IAssociative implementations
(extend-type nil
 IAssociative
   (-assoc [_ k v] {k v})
   (-contains-key? [_ _] false))

(extend-type Vector
 IAssociative
   (-assoc [coll k v] (assoc coll k v))
   (-contains-key? [coll k] (and (int? k) (>= k 0) (< k (count coll)))))

(extend-type Map
 IAssociative
   (-assoc [coll k v] (assoc coll k v))
   (-contains-key? [coll k] (contains? coll k)))

;; ILookup implementations
(extend-type nil
 ILookup
   (-lookup ([_ _] nil) ([_ _ not-found] not-found)))

(extend-type Vector
 ILookup
   (-lookup
     ([coll k] (get coll k))
     ([coll k not-found] (get coll k not-found))))

(extend-type Map
 ILookup
   (-lookup
     ([coll k] (get coll k))
     ([coll k not-found] (get coll k not-found))))

(extend-type Set
 ILookup
   (-lookup
     ([coll k] (get coll k))
     ([coll k not-found] (get coll k not-found))))

;; IIndexed implementations
(extend-type Vector
 IIndexed
   (-nth ([coll n] (nth coll n)) ([coll n not-found] (nth coll n not-found))))

(extend-type List
 IIndexed
   (-nth ([coll n] (nth coll n)) ([coll n not-found] (nth coll n not-found))))

(extend-type String
 IIndexed
   (-nth ([s n] (nth s n)) ([s n not-found] (nth s n not-found))))

;; IDeref implementations
(extend-type Atom
 IDeref
   (-deref [ref] (deref ref)))
(extend-type Delay
 IDeref
   (-deref [ref] (force ref)))
(extend-type Var
 IDeref
   (-deref [ref] (deref ref)))
(extend-type Volatile
 IDeref
   (-deref [ref] (deref ref)))

;; IMeta implementations
(extend-type nil
 IMeta
   (-meta [_] nil))
(extend-type List
 IMeta
   (-meta [obj] (meta obj)))
(extend-type Vector
 IMeta
   (-meta [obj] (meta obj)))
(extend-type Map
 IMeta
   (-meta [obj] (meta obj)))
(extend-type Set
 IMeta
   (-meta [obj] (meta obj)))
(extend-type Symbol
 IMeta
   (-meta [obj] (meta obj)))

;; IWithMeta implementations
(extend-type List
 IWithMeta
   (-with-meta [obj m] (with-meta obj m)))
(extend-type Vector
 IWithMeta
   (-with-meta [obj m] (with-meta obj m)))
(extend-type Map
 IWithMeta
   (-with-meta [obj m] (with-meta obj m)))
(extend-type Set
 IWithMeta
   (-with-meta [obj m] (with-meta obj m)))
(extend-type Symbol
 IWithMeta
   (-with-meta [obj m] (with-meta obj m)))

;; ICounted implementations
(extend-type nil
 ICounted
   (-counted? [_] true))
(extend-type List
 ICounted
   (-counted? [_] true))
(extend-type Vector
 ICounted
   (-counted? [_] true))
(extend-type Map
 ICounted
   (-counted? [_] true))
(extend-type Set
 ICounted
   (-counted? [_] true))
(extend-type String
 ICounted
   (-counted? [_] true))
(extend-type LazySeq
 ICounted
   (-counted? [_] false))

;; ============================================================================
;; Protocol-Aware Predicates
;; ============================================================================
;; These predicates check both built-in types and protocol implementations,
;; allowing user-defined types to participate in the seq abstraction.

(defn seqable?
  "Returns true if x can be converted to a sequence.
   Checks both built-in types and ISeqable protocol implementation."
  [x]
  (or (nil? x)
      (list? x)
      (vector? x)
      (map? x)
      (set? x)
      (string? x)
      (satisfies? ISeqable x)))

(defn seq?
  "Returns true if x is a sequence (list or lazy-seq).
   Checks both built-in types and ISeq protocol implementation."
  [x]
  (or (list? x) (lazy-seq? x) (satisfies? ISeq x)))

(defn associative?
  "Returns true if x supports associative lookup.
   Checks both built-in types and IAssociative protocol implementation."
  [x]
  (or (nil? x) (vector? x) (map? x) (satisfies? IAssociative x)))

(defn indexed?
  "Returns true if x supports indexed (O(1) or near O(1)) access.
   Checks both built-in types and IIndexed protocol implementation."
  [x]
  (or (vector? x) (string? x) (satisfies? IIndexed x)))

(defn counted?
  "Returns true if x has O(1) count.
   Checks ICounted protocol implementation."
  [x]
  (if (satisfies? ICounted x)
    (-counted? x)
    ;; Fallback for built-in types not explicitly extended
    (or (nil? x) (list? x) (vector? x) (map? x) (set? x) (string? x))))

(defn bounded-count
  "If coll is counted? returns its count, else will count at most the first n
   elements of coll using its seq"
  [n coll]
  (if (counted? coll)
    (count coll)
    (loop [i 0
           s (seq coll)]
      (if (and s (< i n)) (recur (inc i) (next s)) i))))

;; ============================================================================
;; Eager Side-Effect Iteration
;; ============================================================================

(defn run!
  "Runs the supplied procedure (via reduce), for purposes of side effects,
   on successive items in the collection. Returns nil."
  [proc coll]
  (reduce (fn [_ x] (proc x) nil) nil coll))

;; ============================================================================
;; Trampoline - Tail-Call Optimisation Helper
;; ============================================================================

(defn trampoline
  "trampoline can be used to convert algorithms requiring mutual recursion
   without stack consumption. Calls f with supplied args, if any. If f returns
   a fn, calls that fn with no arguments, and continues to repeat, until the
   return value is not a fn, then returns that non-fn value.
   Note that if you want to return a fn as a final value, you must wrap it
   in some data structure and unpack it after trampoline returns."
  ([f]
   (loop [ret (f)]
     (if (fn? ret) (recur (ret)) ret)))
  ([f & args] (trampoline #(apply f args))))

;; ============================================================================
;; Tree Traversal
;; ============================================================================

(defn tree-seq
  "Returns a lazy sequence of the nodes in a tree, via a depth-first walk.
   branch? must be a fn of one arg that returns true if passed a node
   that can have children (but may not). children must be a fn of one
   arg that returns a sequence of the children. Will only be called on
   nodes for which branch? returns true. Root is the root node of the tree."
  [branch? children root]
  (let [walk (fn walk [node]
               (lazy-seq (cons node
                               (when (branch? node)
                                 (mapcat walk (children node))))))]
    (walk root)))

;; ============================================================================
;; Probabilistic Filtering
;; ============================================================================

(defn random-sample
  "Returns items from coll with random probability of prob (0.0 - 1.0).
   Returns a transducer when no collection is provided."
  ([prob] (filter (fn [_] (< (rand) prob))))
  ([prob coll] (filter (fn [_] (< (rand) prob)) coll)))

;; ============================================================================
;; Early Termination Transducer
;; ============================================================================

(defn halt-when
  "Returns a transducer that ends transduction when pred returns true
   for an input. When retf is supplied it must be a fn of 2 arguments -
   it will be passed the (completed) result so far and the input that
   triggered the predicate, and its return value (if it does not throw
   an exception) will be the return value of the transducer. If retf
   is not supplied, the input that triggered the predicate will be returned.
   If the predicate never returns true the transduction completes normally."
  ([pred] (halt-when pred nil))
  ([pred retf]
   (fn [rf]
     (fn
       ([] (rf))
       ([result]
        (if (and (map? result) (contains? result ::halt))
          (::halt result)
          (rf result)))
       ([result input]
        (if (pred input)
          (reduced {::halt (if retf (retf (rf result) input) input)})
          (rf result input)))))))
