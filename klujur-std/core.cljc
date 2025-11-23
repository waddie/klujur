;; klujur-std - Standard library macros
;; Copyright (c) 2025 Tom Waddington. MIT licensed.

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

;; ============================================================================
;; Conditional Binding Macros
;; ============================================================================

(defmacro if-let
  "Binds test to bind-vec, evaluates then if truthy, else otherwise."
  ([bind-vec then]
   `(if-let ~bind-vec
            ~then
            nil))
  ([bind-vec then else]
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
  (let [form (bind-vec 0)
        tst  (bind-vec 1)]
    `(let [temp# ~tst]
       (when (some? temp#)
         (let [~form temp#]
           ~@body)))))

(defmacro when-first
  "Binds first element of coll to bind-vec, evaluates body if coll non-empty."
  [bind-vec & body]
  (let [form (bind-vec 0)
        coll (bind-vec 1)]
    `(when-let [s# (seq ~coll)]
       (let [~form (first s#)]
         ~@body))))

;; ============================================================================
;; Conditional Threading Macros
;; ============================================================================

(defmacro cond->
  "Thread expr through forms when tests pass."
  [expr & clauses]
  (let [g (gensym "cond->_")]
    `(let [~g ~expr]
       ~(reduce (fn [acc [test form]]
                  `(if ~test
                     (-> ~acc
                         ~form)
                     ~acc))
                g
                (partition 2 clauses)))))

(defmacro cond->>
  "Thread expr through forms when tests pass (thread last)."
  [expr & clauses]
  (let [g (gensym "cond->>_")]
    `(let [~g ~expr]
       ~(reduce (fn [acc [test form]]
                  `(if ~test
                     (->> ~acc
                          ~form)
                     ~acc))
                g
                (partition 2 clauses)))))

(defmacro some->
  "Thread expr through forms, short-circuiting on nil."
  [expr & forms]
  (let [g (gensym "some->_")]
    `(let [~g ~expr]
       ~(reduce (fn [acc form]
                  `(when (some? ~acc)
                     (-> ~acc
                         ~form)))
                g
                forms))))

(defmacro some->>
  "Thread expr through forms (thread last), short-circuiting on nil."
  [expr & forms]
  (let [g (gensym "some->>_")]
    `(let [~g ~expr]
       ~(reduce (fn [acc form]
                  `(when (some? ~acc)
                     (->> ~acc
                          ~form)))
                g
                forms))))

;; ============================================================================
;; Case and Condp
;; ============================================================================

(defmacro case
  "Dispatch on constant values. No fall-through."
  [expr & clauses]
  (let [default (if (odd? (count clauses))
                  (last clauses)
                  `(throw (ex-info (str "No matching clause: " ~expr)
                                   {:value ~expr})))
        pairs   (if (odd? (count clauses)) (butlast clauses) clauses)
        g       (gensym "case_")]
    `(let [~g ~expr]
       (cond ~@(mapcat (fn [[test then]]
                         (if (list? test)
                           ;; Multiple values
                           `[(or ~@(map (fn [t] `(= ~g ~t)) test)) ~then]
                           `[(= ~g ~test) ~then]))
                (partition 2 pairs))
             :else
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
              (= b :while) `(when ~(first bs)
                              (doseq ~(rest bs)
                                     ~@body))
              :else `(doseq ~(rest bs)
                            ~@body))
        ;; Sequence binding
        (let [sym  (first bindings)
              expr (second bindings)
              more (drop 2 bindings)]
          `(loop [s# (seq ~expr)]
             (when s#
               (let [~sym (first s#)]
                 (doseq ~(vec more)
                        ~@body))
               (recur (next s#)))))))))

(defn- for-emit
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
              (= b :while) `(if ~(first bs) ~(for-emit (rest bs) body-expr) ())
              :else (for-emit (rest bs) body-expr))
        ;; Sequence binding
        (let [sym  (first bindings)
              expr (second bindings)
              more (drop 2 bindings)]
          `(mapcat (fn [~sym] ~(for-emit (vec more) body-expr)) ~expr))))))

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
  "Bind mutually recursive local functions.
   Uses volatiles to enable mutual recursion - each function can call
   the others even though they're defined simultaneously."
  [fnspecs & body]
  (let [names            (map first fnspecs)
        ;; Create gensyms for the volatile references
        vol-syms         (map (fn [n] (gensym (str n "_vol_"))) names)
        ;; Bindings that create volatiles initialized to nil
        vol-bindings     (vec (mapcat (fn [v] [v `(volatile! nil)]) vol-syms))
        ;; Map from name to its volatile symbol
        name->vol        (zipmap names vol-syms)
        ;; Create wrapper functions that deref their volatiles
        wrapper-bindings (vec (mapcat (fn [[name vol]] [name
                                                        `(fn [& args#]
                                                           (apply (deref ~vol)
                                                                  args#))])
                               name->vol))
        ;; Create the actual function implementations
        impl-syms        (map (fn [n] (gensym (str n "_impl_"))) names)
        impl-bindings    (vec (mapcat (fn [spec impl-sym] [impl-sym
                                                           `(fn ~@(rest spec))])
                               fnspecs
                               impl-syms))
        ;; Set the volatiles to the implementations
        set-exprs        (vec (map (fn [vol impl] `(vreset! ~vol ~impl))
                                   vol-syms
                                   impl-syms))]
    `(let ~(vec (concat vol-bindings wrapper-bindings impl-bindings))
          ~@set-exprs
          ~@body)))

;; ============================================================================
;; Lazy Sequence Macros
;; ============================================================================

(defmacro lazy-cat
  "Expands to code that yields a lazy sequence of the concatenation
   of the supplied colls. Each coll expr is not evaluated until it is
   needed."
  [& colls]
  `(lazy-seq (concat ~@colls)))

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
               (cons (f (first s)) (map f (rest s))))))
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
               (let [f (first s)]
                 (if (pred f)
                   (cons f (filter pred (rest s)))
                   (filter pred (rest s))))))))

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

(defn take
  "Returns a lazy sequence of the first n items in coll, or all items if
   there are fewer than n."
  [n coll]
  (lazy-seq (when (pos? n)
              (when-let [s (seq coll)]
                (cons (first s) (take (dec n) (rest s)))))))

(defn drop
  "Returns a lazy sequence of all but the first n items in coll."
  [n coll]
  (lazy-seq (let [s (seq coll)]
              (if (and (pos? n) s) (drop (dec n) (rest s)) s))))

(defn range
  "Returns a lazy seq of nums from start (inclusive) to end (exclusive),
   by step, where start defaults to 0, step to 1, and end to infinity."
  ([] (iterate inc 0))
  ([end] (range 0 end 1))
  ([start end] (range start end 1))
  ([start end step]
   (lazy-seq (if (if (pos? step) (< start end) (> start end))
               (cons start (range (+ start step) end step))
               nil))))

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

(defn partition-all
  "Returns a lazy sequence of lists like partition, but may include
   partitions with fewer than n items at the end."
  ([n coll] (partition-all n n coll))
  ([n step coll]
   (lazy-seq (when-let [s (seq coll)]
               (cons (doall (take n s))
                     (partition-all n step (drop step s)))))))

(defn partition-by
  "Applies f to each value in coll, splitting it each time f returns a
   new value. Returns a lazy seq of partitions."
  [f coll]
  (lazy-seq (when-let [s (seq coll)]
              (let [fst (first s)
                    fv  (f fst)
                    run (doall (cons fst (take-while #(= fv (f %)) (rest s))))]
                (cons run (partition-by f (drop (count run) s)))))))

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

(defn distinct
  "Returns a lazy sequence of the elements of coll with duplicates removed."
  [coll]
  (letfn [(step [seen s]
            (lazy-seq (when-let [s (seq s)]
                        (let [f (first s)]
                          (if (contains? seen f)
                            (step seen (rest s))
                            (cons f (step (conj seen f) (rest s))))))))]
    (step #{} coll)))

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

(defn cat
  "A transducer which concatenates nested collections."
  [rf]
  (fn
    ([] (rf))
    ([result] (rf result))
    ([result input] (reduce rf result input))))

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
  ([n coll]
   (lazy-seq (when-let [s (seq coll)]
               (cons (take n s) (partition-all n (drop n s)))))))

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
                                 (list (concat (list 'refer
                                                     (list 'quote 'klujur.core))
                                               specs))
                                 :else nil)))
        all-forms      (mapcat process-clause clauses)]
    (concat (list 'do) (list (list 'in-ns (list 'quote name))) all-forms)))

;; ============================================================================
;; Transducers
;; ============================================================================

(defn completing
  "Takes a reducing function f of 2 args and returns a fn suitable for
   transduce by adding arity-1 as identity and arity-0 as (f)."
  ([f] (completing f identity))
  ([f cf]
   (fn ([] (f)) ([result] (cf result)) ([result input] (f result input)))))

(defn map-xf
  "Returns a transducer that transforms each element by f."
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result input] (rf result (f input))))))

(defn filter-xf
  "Returns a transducer that filters elements by pred."
  [pred]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result input] (if (pred input) (rf result input) result)))))

(defn remove-xf
  "Returns a transducer that removes elements matching pred."
  [pred]
  (filter-xf (complement pred)))

(defn take-xf
  "Returns a transducer that takes the first n elements."
  [n]
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

(defn drop-xf
  "Returns a transducer that drops the first n elements."
  [n]
  (fn [rf]
    (let [nv (volatile! n)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (let [n @nv]
           (vswap! nv dec)
           (if (pos? n) result (rf result input))))))))

(defn take-while-xf
  "Returns a transducer that takes elements while pred returns true."
  [pred]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result input] (if (pred input) (rf result input) (reduced result))))))

(defn drop-while-xf
  "Returns a transducer that drops elements while pred returns true."
  [pred]
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

(defn take-nth-xf
  "Returns a transducer that takes every nth element."
  [n]
  (fn [rf]
    (let [iv (volatile! -1)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (let [i (vswap! iv inc)]
           (if (zero? (rem i n)) (rf result input) result)))))))

(defn keep-xf
  "Returns a transducer that keeps non-nil results of f."
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result input]
       (let [v (f input)]
         (if (nil? v) result (rf result v)))))))

(defn keep-indexed-xf
  "Returns a transducer that keeps non-nil results of (f index item)."
  [f]
  (fn [rf]
    (let [iv (volatile! -1)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (let [i (vswap! iv inc)
               v (f i input)]
           (if (nil? v) result (rf result v))))))))

(defn map-indexed-xf
  "Returns a transducer that maps (f index item) over elements."
  [f]
  (fn [rf]
    (let [iv (volatile! -1)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (let [i (vswap! iv inc)]
           (rf result (f i input))))))))

(defn dedupe-xf
  "Returns a transducer that removes consecutive duplicates."
  []
  (fn [rf]
    (let [pv (volatile! ::none)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (let [prior @pv]
           (vreset! pv input)
           (if (= prior input) result (rf result input))))))))

(defn distinct-xf
  "Returns a transducer that removes all duplicates."
  []
  (fn [rf]
    (let [seen (volatile! #{})]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result input]
         (if (contains? @seen input)
           result
           (do (vswap! seen conj input) (rf result input))))))))

(defn partition-all-xf
  "Returns a transducer that partitions into groups of n."
  [n]
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

(defn partition-by-xf
  "Returns a transducer that partitions when f changes."
  [f]
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

(defn cat-xf
  "Transducer that concatenates nested collections."
  []
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result input] (reduce rf result input)))))

(defn mapcat-xf
  "Returns a transducer that maps f then concatenates results."
  [f]
  (comp (map-xf f) (cat-xf)))

(defn interpose-xf
  "Returns a transducer that interposes sep between elements."
  [sep]
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
