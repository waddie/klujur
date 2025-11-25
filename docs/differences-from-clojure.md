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

### Chunked Sequences

Klujur supports chunked sequences like Clojure, processing elements in batches of 32 for better performance.

**Chunked sequence functions:**

- `chunked-seq?`, `chunk?` - predicates
- `chunk-first`, `chunk-rest`, `chunk-next` - navigation
- `chunk-cons`, `chunk-buffer`, `chunk-append`, `chunk` - construction
- `chunk-count`, `chunk-nth` - access

**Note:** `range` produces chunked sequences. Other lazy sequences (from `lazy-seq`, `map`, `filter`, etc.) are element-by-element.

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

Klujur’s `letfn` uses volatiles to enable forward references between functions, including mutual recursion.

**How it works internally:**

1. Creates volatiles for each function name
2. Defines functions that dereference the volatiles
3. Assigns the actual function implementations

**Example (mutual recursion):**

```clojure
(letfn [(even? [n] (if (zero? n) true (odd? (dec n))))
        (odd? [n] (if (zero? n) false (even? (dec n))))]
  (even? 10))  ; => true
```

**Performance implications:**

- Each function call involves a volatile dereference
- Suitable for occasional use, not tight loops
- Consider `let` with explicit ordering for performance-critical code

## Integer Overflow

Klujur follows Clojure 1.3+ semantics for integer overflow:

- **Default ops** (`+`, `-`, `*`, `inc`, `dec`) use checked arithmetic and error on overflow
- **Prime variants** (`+'`, `-'`, `*'`, `inc'`, `dec'`) auto-promote to `BigInt`

```clojure
(+ 9223372036854775807 1)   ; Error: Integer overflow
(+' 9223372036854775807 1)  ; => 9223372036854775808N
(*' 9223372036854775807 2)  ; => 18446744073709551614N
```

**Literal auto-promotion:** Integer literals that overflow i64 are automatically promoted to BigInt during parsing:

```clojure
9223372036854775807   ; i64::MAX - stays as Int
9223372036854775808   ; i64::MAX + 1 - auto-promotes to BigInt (prints with N suffix)
```

**Predicates:** `bigint?` tests for BigInt type. `integer?` returns true for both Int and BigInt.

## Threading Model

Klujur is single-threaded by design:

- Uses `Rc<T>` not `Arc<T>`
- Uses `RefCell` not `Mutex`
- No concurrent primitives (agents, futures, promises)
- Atoms work but are not thread-safe

This simplifies the implementation and is appropriate for an embedded scripting language. Do not share Klujur values across threads.
