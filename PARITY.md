# Klujur / Clojure / SCI Feature Parity

A comprehensive comparison of Klujur against Clojure (the reference) and SCI (Small Clojure Interpreter, a comparable embeddable implementation).

## Legend

- ✓ Implemented
- ✗ Not implemented
- ~ Partial / differs from Clojure
- N/A Not applicable

---

## Data Types

| Feature           | Klujur | Clojure | SCI | Notes                                                |
| ----------------- | ------ | ------- | --- | ---------------------------------------------------- |
| Nil               | ✓      | ✓       | ✓   |                                                      |
| Booleans          | ✓      | ✓       | ✓   |                                                      |
| Integers (64-bit) | ✓      | ✓       | ✓   |                                                      |
| Floats (64-bit)   | ✓      | ✓       | ✓   |                                                      |
| Ratios            | ✓      | ✓       | ✓   |                                                      |
| Characters        | ✓      | ✓       | ✓   |                                                      |
| Strings           | ✓      | ✓       | ✓   |                                                      |
| Symbols           | ✓      | ✓       | ✓   | Interned                                             |
| Keywords          | ✓      | ✓       | ✓   | Interned                                             |
| Lists             | ✓      | ✓       | ✓   | **Differs**: backed by `im::Vector`, not linked list |
| Vectors           | ✓      | ✓       | ✓   | Persistent via `im::Vector`                          |
| Maps              | ✓      | ✓       | ✓   | **Differs**: ordered (`im::OrdMap`), not hash-based  |
| Sets              | ✓      | ✓       | ✓   | **Differs**: ordered (`im::OrdSet`), not hash-based  |
| Regex             | ✓      | ✓       | ✓   | `#"pattern"` syntax                                  |
| BigInt            | ✗      | ✓       | ✗   |                                                      |
| BigDecimal        | ✗      | ✓       | ✗   |                                                      |

## Special Forms

| Feature                         | Klujur | Clojure | SCI | Notes                      |
| ------------------------------- | ------ | ------- | --- | -------------------------- |
| `def`                           | ✓      | ✓       | ✓   |                            |
| `if`                            | ✓      | ✓       | ✓   |                            |
| `do`                            | ✓      | ✓       | ✓   |                            |
| `let` / `let*`                  | ✓      | ✓       | ✓   |                            |
| `quote`                         | ✓      | ✓       | ✓   |                            |
| `fn` / `fn*`                    | ✓      | ✓       | ✓   | Multi-arity, destructuring |
| `loop` / `recur`                | ✓      | ✓       | ✓   | With TCO                   |
| `throw`                         | ✓      | ✓       | ✓   |                            |
| `try` / `catch` / `finally`     | ✓      | ✓       | ✓   |                            |
| `var`                           | ✓      | ✓       | ✓   |                            |
| `set!`                          | ✓      | ✓       | ✓   | For dynamic vars           |
| `binding`                       | ✓      | ✓       | ✓   | Dynamic binding            |
| `lazy-seq`                      | ✓      | ✓       | ✓   |                            |
| `defmacro`                      | ✓      | ✓       | ✓   |                            |
| `macroexpand` / `macroexpand-1` | ✓      | ✓       | ✓   |                            |
| `in-ns`                         | ✓      | ✓       | ✓   |                            |
| `defmulti` / `defmethod`        | ✓      | ✓       | ✓   |                            |
| `defprotocol`                   | ✓      | ✓       | ✓   |                            |
| `extend-type`                   | ✓      | ✓       | ✓   |                            |
| `defrecord`                     | ✓      | ✓       | ✓   |                            |
| `deftype`                       | ✗      | ✓       | ✗   |                            |
| `reify`                         | ✗      | ✓       | ✓   |                            |
| `letfn`                         | ~      | ✓       | ✓   | No mutual recursion        |

## Core Macros (klujur-std/core.cljc)

| Feature                 | Klujur | Clojure | SCI | Notes              |
| ----------------------- | ------ | ------- | --- | ------------------ |
| `defn` / `defn-`        | ✓      | ✓       | ✓   |                    |
| `when` / `when-not`     | ✓      | ✓       | ✓   |                    |
| `if-not`                | ✓      | ✓       | ✓   |                    |
| `cond`                  | ✓      | ✓       | ✓   |                    |
| `case`                  | ✓      | ✓       | ✓   |                    |
| `condp`                 | ~      | ✓       | ✓   | `:>>` handling broken |
| `if-let` / `when-let`   | ✓      | ✓       | ✓   |                    |
| `if-some` / `when-some` | ✓      | ✓       | ✓   |                    |
| `when-first`            | ✓      | ✓       | ✓   |                    |
| `->` / `->>`            | ✓      | ✓       | ✓   |                    |
| `as->`                  | ✓      | ✓       | ✓   |                    |
| `cond->` / `cond->>`    | ~      | ✓       | ✓   | Slightly different expansion |
| `some->` / `some->>`    | ~      | ✓       | ✓   | Slightly different expansion |
| `and` / `or`            | ✓      | ✓       | ✓   |                    |
| `doto`                  | ✓      | ✓       | ✓   |                    |
| `..`                    | ✗      | ✓       | ✓   | Java interop       |
| `delay`                 | ✓      | ✓       | ✓   |                    |
| `time`                  | ✓      | ✓       | ✓   |                    |
| `assert`                | ✓      | ✓       | ✓   |                    |
| `comment`               | ✓      | ✓       | ✓   |                    |
| `declare`               | ✓      | ✓       | ✓   |                    |
| `ns`                    | ✓      | ✓       | ✓   | `:require`, `:use` |
| `lazy-cat`              | ✓      | ✓       | ✓   |                    |
| `for`                   | ✓      | ✓       | ✓   | List comprehension |
| `doseq`                 | ✓      | ✓       | ✓   |                    |
| `dotimes`               | ✓      | ✓       | ✓   |                    |
| `while`                 | ✓      | ✓       | ✓   |                    |

## Sequences

| Feature                       | Klujur | Clojure | SCI | Notes |
| ----------------------------- | ------ | ------- | --- | ----- |
| `seq`                         | ✓      | ✓       | ✓   |       |
| `first` / `rest` / `next`     | ✓      | ✓       | ✓   |       |
| `cons`                        | ✓      | ✓       | ✓   |       |
| `conj`                        | ✓      | ✓       | ✓   |       |
| `count`                       | ✓      | ✓       | ✓   |       |
| `nth`                         | ✓      | ✓       | ✓   |       |
| `last` / `butlast`            | ✓      | ✓       | ✓   |       |
| `second` / `ffirst` / `fnext` | ✓      | ✓       | ✓   |       |
| `nfirst` / `nnext`            | ✓      | ✓       | ✓   |       |
| `empty?` / `not-empty`        | ✓      | ✓       | ✓   |       |
| `empty`                       | ✓      | ✓       | ✓   |       |

## Lazy Sequences

| Feature                       | Klujur | Clojure | SCI | Notes |
| ----------------------------- | ------ | ------- | --- | ----- |
| `lazy-seq`                    | ✓      | ✓       | ✓   |       |
| `map` (lazy)                  | ✓      | ✓       | ✓   |       |
| `filter` / `remove` (lazy)    | ✓      | ✓       | ✓   |       |
| `take` / `drop`               | ✓      | ✓       | ✓   |       |
| `take-while` / `drop-while`   | ✓      | ✓       | ✓   |       |
| `take-nth`                    | ✓      | ✓       | ✓   |       |
| `take-last` / `drop-last`     | ✓      | ✓       | ✓   |       |
| `concat`                      | ✓      | ✓       | ✓   |       |
| `mapcat`                      | ✓      | ✓       | ✓   |       |
| `cycle`                       | ✓      | ✓       | ✓   |       |
| `repeat`                      | ✓      | ✓       | ✓   |       |
| `iterate`                     | ✓      | ✓       | ✓   |       |
| `repeatedly`                  | ✓      | ✓       | ✓   |       |
| `range` (infinite)            | ✓      | ✓       | ✓   |       |
| `interleave` / `interpose`    | ✓      | ✓       | ✓   |       |
| `partition` / `partition-all` | ✓      | ✓       | ✓   |       |
| `partition-by`                | ✓      | ✓       | ✓   |       |
| `split-at` / `split-with`     | ✓      | ✓       | ✓   |       |
| `keep` / `keep-indexed`       | ✓      | ✓       | ✓   |       |
| `map-indexed`                 | ✓      | ✓       | ✓   |       |
| `flatten`                     | ✓      | ✓       | ✓   |       |
| `distinct`                    | ✓      | ✓       | ✓   |       |
| `reductions`                  | ✓      | ✓       | ✓   |       |
| `realized?`                   | ✓      | ✓       | ✓   |       |
| `doall` / `dorun`             | ✓      | ✓       | ✓   |       |
| Chunked sequences             | ✗      | ✓       | ✗   |       |

## Higher-Order Functions

| Feature                   | Klujur | Clojure | SCI | Notes |
| ------------------------- | ------ | ------- | --- | ----- |
| `apply`                   | ✓      | ✓       | ✓   |       |
| `reduce`                  | ✓      | ✓       | ✓   |       |
| `reduce-kv`               | ✓      | ✓       | ✓   |       |
| `comp`                    | ✓      | ✓       | ✓   |       |
| `partial`                 | ✓      | ✓       | ✓   |       |
| `constantly`              | ✓      | ✓       | ✓   |       |
| `identity`                | ✓      | ✓       | ✓   |       |
| `complement`              | ✓      | ✓       | ✓   |       |
| `juxt`                    | ✓      | ✓       | ✓   |       |
| `fnil`                    | ✓      | ✓       | ✓   |       |
| `every?` / `some`         | ✓      | ✓       | ✓   |       |
| `not-every?` / `not-any?` | ✓      | ✓       | ✓   |       |
| `every-pred` / `some-fn`  | ✓      | ✓       | ✓   |       |
| `memoize`                 | ✓      | ✓       | ✓   |       |

## Eager Sequence Functions

| Feature            | Klujur | Clojure | SCI | Notes |
| ------------------ | ------ | ------- | --- | ----- |
| `mapv` / `filterv` | ✓      | ✓       | ✓   |       |
| `into`             | ✓      | ✓       | ✓   |       |
| `reverse`          | ✓      | ✓       | ✓   |       |
| `sort` / `sort-by` | ✓      | ✓       | ✓   |       |
| `frequencies`      | ✓      | ✓       | ✓   |       |
| `group-by`         | ✓      | ✓       | ✓   |       |
| `rseq`             | ✓      | ✓       | ✓   |       |

## Collections

| Feature                           | Klujur | Clojure | SCI | Notes              |
| --------------------------------- | ------ | ------- | --- | ------------------ |
| `list` / `vector`                 | ✓      | ✓       | ✓   |                    |
| `hash-map` / `hash-set`           | ✓      | ✓       | ✓   |                    |
| `sorted-map` / `sorted-set`       | ✓      | ✓       | ✓   |                    |
| `sorted-map-by` / `sorted-set-by` | ✗      | ✓       | ✓   | Custom comparators |
| `vec` / `set`                     | ✓      | ✓       | ✓   |                    |
| `list*`                           | ✓      | ✓       | ✓   |                    |
| `zipmap`                          | ✓      | ✓       | ✓   |                    |
| `get` / `get-in`                  | ✓      | ✓       | ✓   |                    |
| `assoc` / `assoc-in`              | ✓      | ✓       | ✓   |                    |
| `dissoc`                          | ✓      | ✓       | ✓   |                    |
| `update` / `update-in`            | ✓      | ✓       | ✓   |                    |
| `update-keys` / `update-vals`     | ✓      | ✓       | ✓   | Clojure 1.11+      |
| `keys` / `vals`                   | ✓      | ✓       | ✓   |                    |
| `find`                            | ✓      | ✓       | ✓   |                    |
| `contains?`                       | ✓      | ✓       | ✓   |                    |
| `select-keys`                     | ✓      | ✓       | ✓   |                    |
| `merge` / `merge-with`            | ✓      | ✓       | ✓   |                    |
| `peek` / `pop`                    | ✓      | ✓       | ✓   |                    |
| `disj`                            | ✓      | ✓       | ✓   |                    |
| Transient collections             | ✗      | ✓       | ✗   |                    |

## Transducers

| Feature                        | Klujur | Clojure | SCI | Notes |
| ------------------------------ | ------ | ------- | --- | ----- |
| `transduce`                    | ✓      | ✓       | ✓   |       |
| `into` (3-arity)               | ✓      | ✓       | ✓   |       |
| `sequence` (2-arity)           | ✗      | ✓       | ✓   |       |
| `eduction`                     | ✗      | ✓       | ✓   |       |
| `completing`                   | ✓      | ✓       | ✓   |       |
| `reduced` / `reduced?`         | ✓      | ✓       | ✓   |       |
| `unreduced` / `ensure-reduced` | ✓      | ✓       | ✓   |       |
| `(map f)` transducer           | ✓      | ✓       | ✓   |       |
| `(filter pred)` transducer     | ✓      | ✓       | ✓   |       |
| `(take n)` transducer          | ✓      | ✓       | ✓   |       |
| `(drop n)` transducer          | ✓      | ✓       | ✓   |       |
| `(partition-all n)` transducer | ✓      | ✓       | ✓   |       |
| `(partition-by f)` transducer  | ✓      | ✓       | ✓   |       |
| `(dedupe)` transducer          | ✓      | ✓       | ✓   |       |
| `(distinct)` transducer        | ✓      | ✓       | ✓   |       |
| `cat` transducer               | ~      | ✓       | ✓   | Wrong arity (takes 0 args, should take rf) |
| `(mapcat f)` transducer        | ✓      | ✓       | ✓   |       |
| `(interpose sep)` transducer   | ✓      | ✓       | ✓   |       |

## Multimethods

| Feature            | Klujur | Clojure | SCI | Notes |
| ------------------ | ------ | ------- | --- | ----- |
| `defmulti`         | ✓      | ✓       | ✓   |       |
| `defmethod`        | ✓      | ✓       | ✓   |       |
| `:default` method  | ✓      | ✓       | ✓   |       |
| `methods`          | ✓      | ✓       | ✓   |       |
| `get-method`       | ✓      | ✓       | ✓   |       |
| `remove-method`    | ✓      | ✓       | ✓   |       |
| `prefer-method`    | ✓      | ✓       | ✓   |       |
| Hierarchy dispatch | ✓      | ✓       | ✓   |       |

## Hierarchies

| Feature          | Klujur | Clojure | SCI | Notes |
| ---------------- | ------ | ------- | --- | ----- |
| `derive`         | ✓      | ✓       | ✓   |       |
| `underive`       | ✓      | ✓       | ✓   |       |
| `isa?`           | ✓      | ✓       | ✓   |       |
| `parents`        | ✓      | ✓       | ✓   |       |
| `ancestors`      | ✓      | ✓       | ✓   |       |
| `descendants`    | ✓      | ✓       | ✓   |       |
| `make-hierarchy` | ✓      | ✓       | ✓   |       |

## Protocols

| Feature             | Klujur | Clojure | SCI | Notes |
| ------------------- | ------ | ------- | --- | ----- |
| `defprotocol`       | ✓      | ✓       | ✓   |       |
| `extend-type`       | ✓      | ✓       | ✓   |       |
| `extend-protocol`   | ✓      | ✓       | ✓   |       |
| `extend` (map form) | ✗      | ✓       | ✓   |       |
| `satisfies?`        | ✓      | ✓       | ✓   |       |
| `extends?`          | ✓      | ✓       | ✓   |       |

## Atoms & State

| Feature                            | Klujur | Clojure | SCI | Notes |
| ---------------------------------- | ------ | ------- | --- | ----- |
| `atom`                             | ✓      | ✓       | ✓   |       |
| `reset!` / `swap!`                 | ✓      | ✓       | ✓   |       |
| `reset-vals!` / `swap-vals!`       | ✓      | ✓       | ✓   |       |
| `compare-and-set!`                 | ✓      | ✓       | ✓   |       |
| `add-watch` / `remove-watch`       | ✓      | ✓       | ✓   |       |
| `set-validator!` / `get-validator` | ✓      | ✓       | ✓   |       |
| Agents                             | ✗      | ✓       | ✗   |       |
| Refs / STM                         | ✗      | ✓       | ✗   |       |
| Futures                            | ✗      | ✓       | ✗   |       |
| Promises                           | ✗      | ✓       | ✗   |       |

## Volatiles

| Feature     | Klujur | Clojure | SCI | Notes |
| ----------- | ------ | ------- | --- | ----- |
| `volatile!` | ✓      | ✓       | ✓   |       |
| `volatile?` | ✓      | ✓       | ✓   |       |
| `vreset!`   | ✓      | ✓       | ✓   |       |
| `vswap!`    | ✓      | ✓       | ✓   |       |

## Delays

| Feature     | Klujur | Clojure | SCI | Notes |
| ----------- | ------ | ------- | --- | ----- |
| `delay`     | ✓      | ✓       | ✓   |       |
| `delay?`    | ✓      | ✓       | ✓   |       |
| `force`     | ✓      | ✓       | ✓   |       |
| `realized?` | ✓      | ✓       | ✓   |       |

## Metadata

| Feature           | Klujur | Clojure | SCI | Notes |
| ----------------- | ------ | ------- | --- | ----- |
| `meta`            | ✓      | ✓       | ✓   |       |
| `with-meta`       | ✓      | ✓       | ✓   |       |
| `vary-meta`       | ✓      | ✓       | ✓   |       |
| `alter-meta!`     | ✓      | ✓       | ✓   |       |
| `reset-meta!`     | ✓      | ✓       | ✓   |       |
| `^` reader syntax | ✓      | ✓       | ✓   |       |

## Namespaces

| Feature      | Klujur | Clojure | SCI | Notes                      |
| ------------ | ------ | ------- | --- | -------------------------- |
| `ns`         | ✓      | ✓       | ✓   |                            |
| `in-ns`      | ✓      | ✓       | ✓   |                            |
| `require`    | ✓      | ✓       | ✓   | `:as`, `:refer`, `:reload` |
| `use`        | ✓      | ✓       | ✓   | Deprecated                 |
| `refer`      | ✓      | ✓       | ✓   |                            |
| `alias`      | ✓      | ✓       | ✓   |                            |
| `all-ns`     | ✓      | ✓       | ✓   |                            |
| `find-ns`    | ✓      | ✓       | ✓   |                            |
| `create-ns`  | ✓      | ✓       | ✓   |                            |
| `remove-ns`  | ✓      | ✓       | ✓   |                            |
| `the-ns`     | ✓      | ✓       | ✓   |                            |
| `ns-name`    | ✓      | ✓       | ✓   |                            |
| `ns-publics` | ✓      | ✓       | ✓   |                            |
| `ns-interns` | ✓      | ✓       | ✓   |                            |
| `load-file`  | ✓      | ✓       | ✓   |                            |

## I/O

| Feature                    | Klujur | Clojure | SCI | Notes              |
| -------------------------- | ------ | ------- | --- | ------------------ |
| `print` / `println`        | ✓      | ✓       | ✓   |                    |
| `pr` / `prn`               | ✓      | ✓       | ✓   |                    |
| `str` / `pr-str`           | ✓      | ✓       | ✓   |                    |
| `format`                   | ✓      | ✓       | ✓   |                    |
| `slurp` / `spit`           | ✓      | ✓       | ✓   |                    |
| `read-string`              | ✓      | ✓       | ✓   |                    |
| `read`                     | ✗      | ✓       | ✓   | Reader from stream |
| `*in*` / `*out*` / `*err*` | ✗      | ✓       | ✓   |                    |

## Evaluation

| Feature       | Klujur | Clojure | SCI | Notes |
| ------------- | ------ | ------- | --- | ----- |
| `eval`        | ✓      | ✓       | ✓   |       |
| `load-string` | ✓      | ✓       | ✓   |       |
| `load-file`   | ✓      | ✓       | ✓   |       |

## Exceptions

| Feature                     | Klujur | Clojure | SCI | Notes |
| --------------------------- | ------ | ------- | --- | ----- |
| `try` / `catch` / `finally` | ✓      | ✓       | ✓   |       |
| `throw`                     | ✓      | ✓       | ✓   |       |
| `ex-info`                   | ✓      | ✓       | ✓   |       |
| `ex-message`                | ✓      | ✓       | ✓   |       |
| `ex-data`                   | ✓      | ✓       | ✓   |       |

## Interop

| Feature            | Klujur | Clojure | SCI | Notes                |
| ------------------ | ------ | ------- | --- | -------------------- |
| Java interop       | N/A    | ✓       | N/A | Not applicable       |
| JavaScript interop | N/A    | N/A     | ✓   | SCI targets JS       |
| Rust FFI           | ✗      | N/A     | N/A | Planned (Engine API) |

## Threading Model

| Feature                 | Klujur | Clojure | SCI | Notes                                        |
| ----------------------- | ------ | ------- | --- | -------------------------------------------- |
| Thread-safe collections | ~      | ✓       | ~   | Klujur uses `Rc`/`RefCell` (single-threaded) |
| Concurrent primitives   | ✗      | ✓       | ✗   |                                              |
| `pmap`                  | ✗      | ✓       | ✗   |                                              |
| `future` / `promise`    | ✗      | ✓       | ✗   |                                              |
| `agent`                 | ✗      | ✓       | ✗   |                                              |

---

## Key Differences from Clojure

### Collection Implementation

| Aspect              | Klujur                    | Clojure                         |
| ------------------- | ------------------------- | ------------------------------- |
| List backing        | `im::Vector`              | Linked list (PersistentList)    |
| Map/Set ordering    | Ordered (OrdMap/OrdSet)   | Hash-based (unordered)          |
| Reference type      | `Rc<T>` (single-threaded) | Thread-safe                     |
| Interior mutability | `RefCell`                 | Lock-free concurrent structures |

### Semantic Differences

1. **List performance**: Klujur lists have O(log n) `first`/`rest` vs O(1) in Clojure
2. **Map iteration order**: Klujur maps iterate in key order, Clojure in insertion order
3. **No chunked sequences**: Klujur realises one element at a time
4. **Single-threaded**: No concurrent primitives (atoms work but aren't thread-safe)

### Missing Features

1. **Embedding API** - Planned
2. **Transient collections** - Not planned for v1.0
3. **Concurrency primitives** - Not planned (single-threaded by design)
4. **Java/JS interop** - Not applicable

---

## Known Issues (Code Review 2025-11-23)

Issues identified during code review that affect parity. See `CODE_REVIEW.md` for full details.

### Critical Bugs

| Issue | Location | Impact |
|-------|----------|--------|
| `condp` `:>>` handling broken | `core.cljc:191-212` | `:>>` threading form doesn't work |
| `letfn` no mutual recursion | `core.cljc:268-275` | Can't define mutually recursive functions |
| `cat` wrong arity | `core.cljc:741-748` | Breaks transducer composition patterns |
| Parser positions always `1:1` | `parser.rs:46-64` | Error locations useless |
| Ratio comparison overflow | `value.rs:2372-2375` | Incorrect ordering for large ratios |
| Float Hash/Eq/Ord inconsistent | `value.rs` | Violates Rust trait contracts |

### Semantic Differences

| Feature | Difference |
|---------|------------|
| `cond->` / `cond->>` | Uses `reduce` instead of rebinding pattern |
| `some->` / `some->>` | Uses `reduce` instead of rebinding pattern |

### Missing (Despite Being Tested)

- `for` macro - list comprehension (tests exist, implementation missing)
