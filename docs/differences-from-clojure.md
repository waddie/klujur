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

### Maps and Sets Are Ordered

Klujur maps use `im::OrdMap` and sets use `im::OrdSet`, providing iteration in **key order** (sorted), not insertion order.

**Implications:**

- `keys`, `vals`, and `seq` return elements in sorted key order
- Iteration order is deterministic based on key comparison
- No equivalent to Clojure’s `array-map` (insertion-ordered small maps)

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

**When this matters:**

- Side-effecting lazy sequences behave more predictably
- Performance-sensitive code may need `mapv`/`filterv` for bulk operations
- Memory pressure may differ for large lazy sequences

## Exception Handling

### Catch Uses `:default`, Not Class Names

Klujur’s `try`/`catch` uses `:default` to catch all exceptions, not Java class names.

**Catch syntax:**

- `(catch :default e body)` - catches any exception
- No type-specific catching (all exceptions are caught the same way)

**When this matters:**

- Port Clojure code that catches specific exception types
- Use `ex-data` to distinguish error types:

## `letfn` Performance Characteristics

### Implementation Uses Volatiles

Klujur’s `letfn` uses volatiles to enable forward references between functions.

**How it works internally:**

1. Creates volatiles for each function name
2. Defines functions that dereference the volatiles
3. Assigns the actual function implementations

**Performance implications:**

- Each function call involves a volatile dereference
- Suitable for occasional use, not tight loops
- Consider `let` with explicit ordering for performance-critical code:

**Note:** Klujur’s `letfn` does not support mutual recursion (functions calling each other). This is a known limitation.

## Integer Overflow

Unlike Clojure which auto-promotes to `BigInteger`, Klujur uses checked arithmetic and returns an error on overflow.

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
