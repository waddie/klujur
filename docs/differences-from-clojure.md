# Differences from Clojure

This document details Klujur-specific behaviours that differ from standard Clojure. Understanding these differences is important when porting Clojure code or when Clojure documentation doesn’t match observed behaviour.

## Collection Implementation

### Lists Use `im::Vector`

Klujur lists are backed by `im::Vector`, not linked lists as in Clojure.

**Implications:**

| Operation | Clojure (Linked List) | Klujur (`im::Vector`) |
| --------- | --------------------- | --------------------- |
| `first`   | O(1)                  | O(log n)              |
| `rest`    | O(1)                  | O(log n)              |
| `conj`    | O(1) prepend          | O(log n) prepend      |
| `nth`     | O(n)                  | O(log n)              |
| `count`   | O(n) or cached        | O(1)                  |

**Why this matters:**

- Algorithms that heavily use `first`/`rest` may be slower
- Random access via `nth` is faster
- Memory layout is more cache-friendly

```clojure
;; This is faster in Klujur than Clojure:
(nth my-list 1000)

;; This may be slower in Klujur:
(loop [coll my-list]
  (when (seq coll)
    (recur (rest coll))))
```

### Maps and Sets Are Ordered

Klujur maps use `im::OrdMap` and sets use `im::OrdSet`, providing iteration in **key order** (sorted), not insertion order.

**Implications:**

- `keys`, `vals`, and `seq` return elements in sorted key order
- Iteration order is deterministic based on key comparison
- No equivalent to Clojure’s `array-map` (insertion-ordered small maps)

```clojure
;; Clojure: iteration in insertion order
(keys {:b 2 :a 1 :c 3})  ; => (:b :a :c)

;; Klujur: iteration in key order
(keys {:b 2 :a 1 :c 3})  ; => (:a :b :c)
```

**When this matters:**

- Code that relies on insertion order will behave differently
- JSON round-tripping may reorder keys
- `hash-map` and `sorted-map` produce the same iteration order

## Lazy Sequences

### Element-by-Element Evaluation (Not Chunked)

Klujur lazy sequences realise one element at a time. Clojure uses 32-element chunks for performance.

**Implications:**

| Aspect       | Clojure (Chunked)           | Klujur (Element-wise)     |
| ------------ | --------------------------- | ------------------------- |
| Side effects | May evaluate extra elements | Precise control           |
| Performance  | Better for bulk operations  | More overhead per element |
| Memory       | 32 elements at once         | One element at a time     |

```clojure
;; In Clojure, this may print more than 5 items due to chunking:
(take 5 (map #(do (println %) %) (range 100)))

;; In Klujur, exactly 5 items are printed
```

**When this matters:**

- Side-effecting lazy sequences behave more predictably
- Performance-sensitive code may need `mapv`/`filterv` for bulk operations
- Memory pressure may differ for large lazy sequences

## Exception Handling

### Catch Uses `:default`, Not Class Names

Klujur’s `try`/`catch` uses `:default` to catch all exceptions, not Java class names.

```clojure
;; Clojure (JVM):
(try
  (throw (ex-info "error" {:type :my-error}))
  (catch clojure.lang.ExceptionInfo e
    (ex-data e)))

;; Klujur:
(try
  (throw (ex-info "error" {:type :my-error}))
  (catch :default e
    (ex-data e)))
```

**Catch syntax:**

- `(catch :default e body)` - catches any exception
- No type-specific catching (all exceptions are caught the same way)

**When this matters:**

- Port Clojure code that catches specific exception types
- Use `ex-data` to distinguish error types:

```clojure
(try
  (do-something)
  (catch :default e
    (case (:type (ex-data e))
      :validation (handle-validation e)
      :io (handle-io e)
      (throw e))))  ; re-throw if unhandled
```

## `letfn` Performance Characteristics

### Implementation Uses Volatiles

Klujur’s `letfn` uses volatiles to enable forward references between functions.

```clojure
(letfn [(f [x] (g x))   ; f can reference g
        (g [x] (* x 2))]
  (f 5))
```

**How it works internally:**

1. Creates volatiles for each function name
2. Defines functions that dereference the volatiles
3. Assigns the actual function implementations

**Performance implications:**

- Each function call involves a volatile dereference
- Suitable for occasional use, not tight loops
- Consider `let` with explicit ordering for performance-critical code:

```clojure
;; Performance-sensitive alternative:
(let [g (fn [x] (* x 2))
      f (fn [x] (g x))]
  (f 5))
```

**Note:** Klujur’s `letfn` does not support mutual recursion (functions calling each other). This is a known limitation.

## Integer Overflow

Unlike Clojure which auto-promotes to `BigInteger`, Klujur uses checked arithmetic and returns an error on overflow.

```clojure
;; Clojure: auto-promotes to BigInt
(+ 9223372036854775807 1)  ; => 9223372036854775808N

;; Klujur: returns error
(+ 9223372036854775807 1)  ; => Error: integer overflow
```

**Affected operations:** `+`, `-`, `*`, `inc`, `dec`, `abs` (for `i64::MIN`), unary negation (for `i64::MIN`).

**Workarounds:**

- Use ratios for arbitrary precision: `(+ 9223372036854775807/1 1/1)`
- Check bounds before operations
- Operations involving floats do not check for overflow

## Threading Model

Klujur is single-threaded by design:

- Uses `Rc<T>` not `Arc<T>`
- Uses `RefCell` not `Mutex`
- No concurrent primitives (agents, futures, promises)
- Atoms work but are not thread-safe

This simplifies the implementation and is appropriate for an embedded scripting language. Do not share Klujur values across threads.
