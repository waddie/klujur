# Klujur-specific built-in functions

This document lists built-in functions in Klujur that are not part of standard Clojure. These functions are organised into dedicated namespaces.

## klujur.math

Mathematical functions. In Clojure, these typically require Java interop (`Math/sqrt`, etc.).

```clojure
(require '[klujur.math :as m])
```

### Roots and powers

| Function | Signature        | Description                      |
| -------- | ---------------- | -------------------------------- |
| `sqrt`   | `(sqrt n)`       | Square root                      |
| `cbrt`   | `(cbrt n)`       | Cube root                        |
| `pow`    | `(pow base exp)` | Raise base to the power exp      |
| `exp`    | `(exp x)`        | e raised to the power x          |
| `hypot`  | `(hypot x y)`    | `sqrt(x² + y²)` without overflow |

### Trigonometric functions

All trigonometric functions work in radians.

| Function | Signature     | Description              |
| -------- | ------------- | ------------------------ |
| `sin`    | `(sin x)`     | Sine                     |
| `cos`    | `(cos x)`     | Cosine                   |
| `tan`    | `(tan x)`     | Tangent                  |
| `asin`   | `(asin x)`    | Arc sine                 |
| `acos`   | `(acos x)`    | Arc cosine               |
| `atan`   | `(atan x)`    | Arc tangent              |
| `atan2`  | `(atan2 y x)` | Two-argument arc tangent |
| `sinh`   | `(sinh x)`    | Hyperbolic sine          |
| `cosh`   | `(cosh x)`    | Hyperbolic cosine        |
| `tanh`   | `(tanh x)`    | Hyperbolic tangent       |

### Logarithms

| Function | Signature   | Description                |
| -------- | ----------- | -------------------------- |
| `log`    | `(log x)`   | Natural logarithm (base e) |
| `log10`  | `(log10 x)` | Base-10 logarithm          |
| `log2`   | `(log2 x)`  | Base-2 logarithm           |

### Rounding

| Function | Signature   | Description                        |
| -------- | ----------- | ---------------------------------- |
| `floor`  | `(floor x)` | Largest integer not greater than x |
| `ceil`   | `(ceil x)`  | Smallest integer not less than x   |
| `round`  | `(round x)` | Round to nearest integer (half up) |
| `trunc`  | `(trunc x)` | Truncate toward zero               |

### Miscellaneous

| Function     | Signature          | Description                  |
| ------------ | ------------------ | ---------------------------- |
| `signum`     | `(signum x)`       | Sign of x: -1.0, 0.0, or 1.0 |
| `nan?`       | `(nan? x)`         | True if x is NaN             |
| `infinite?`  | `(infinite? x)`    | True if x is infinite        |
| `to-radians` | `(to-radians deg)` | Convert degrees to radians   |
| `to-degrees` | `(to-degrees rad)` | Convert radians to degrees   |

### Constants

| Function | Signature | Description                 |
| -------- | --------- | --------------------------- |
| `pi`     | `(pi)`    | The constant π (3.14159...) |
| `e`      | `(e)`     | Euler's number (2.71828...) |

### Examples

```clojure
(require '[klujur.math :as m])

(m/sqrt 16)             ; => 4.0
(m/pow 2 10)            ; => 1024.0
(m/sin (/ (m/pi) 2))    ; => 1.0
(m/log (m/e))           ; => 1.0
(m/to-degrees (m/pi))   ; => 180.0
(m/nan? (/ 0.0 0.0))    ; => true
```

## klujur.time

Functions for getting the current time. In Clojure, these require Java interop (`System/currentTimeMillis`, etc.).

```clojure
(require '[klujur.time :as t])
```

| Function      | Signature       | Description                                   |
| ------------- | --------------- | --------------------------------------------- |
| `system-time` | `(system-time)` | Current time in milliseconds since Unix epoch |
| `now-millis`  | `(now-millis)`  | Alias for `system-time`                       |
| `now-micros`  | `(now-micros)`  | Current time in microseconds since Unix epoch |
| `now-nanos`   | `(now-nanos)`   | Current time in nanoseconds since Unix epoch  |
| `now-secs`    | `(now-secs)`    | Current time in seconds since Unix epoch      |

### Examples

```clojure
(require '[klujur.time :as t])

(t/now-millis)  ; => 1732345678901
(t/now-secs)    ; => 1732345678

;; Timing code execution
(let [start (t/now-nanos)
      _     (dotimes [_ 1000000] (+ 1 2))
      end   (t/now-nanos)]
  (println "Elapsed:" (- end start) "ns"))
```

## Klujur.io

Additional I/O functions beyond standard Clojure.

```clojure
(require '[klujur.io :as io])
```

| Function    | Signature                 | Description                                 |
| ----------- | ------------------------- | ------------------------------------------- |
| `read-line` | `(read-line)`             | Read a line from stdin (returns nil on EOF) |
| `flush`     | `(flush)`                 | Flush stdout                                |
| `getenv`    | `(getenv name)`           | Get environment variable (nil if not set)   |
| `setenv`    | `(setenv name value)`     | Set environment variable                    |
| `exit`      | `(exit)` or `(exit code)` | Exit the process with optional exit code    |

### Examples

```clojure
(require '[klujur.io :as io])

;; Interactive input
(print "Enter your name: ")
(io/flush)
(let [name (io/read-line)]
  (println "Hello," name))

;; Environment variables
(io/getenv "HOME")           ; => "/Users/tom"
(io/setenv "MY_VAR" "hello")
(io/getenv "MY_VAR")         ; => "hello"

;; Exit
(io/exit)      ; Exit with code 0
(io/exit 1)    ; Exit with code 1
```

## klujur.core extensions

These functions remain in `klujur.core` (available without requiring):

| Function            | Signature               | Description                                              |
| ------------------- | ----------------------- | -------------------------------------------------------- |
| `set-print-length!` | `(set-print-length! n)` | Set max elements to print in sequences (nil = unlimited) |
| `get-print-length`  | `(get-print-length)`    | Get current print-length setting                         |
| `sorted-map-by`     | `(sorted-map-by c & k)` | Create sorted map with custom comparator                 |
| `sorted-set-by`     | `(sorted-set-by c & k)` | Create sorted set with custom comparator                 |

### Custom comparator collections

The comparator function can return either:

- An integer: negative if a < b, zero if a = b, positive if a > b
- A boolean: true if a < b (requires two calls to distinguish equal from greater)

```clojure
;; Reverse-sorted map
(sorted-map-by > 1 :a 2 :b 3 :c)
; => {3 :c, 2 :b, 1 :a}

;; Case-insensitive string set
(defn case-insensitive [a b]
  (compare (lower-case a) (lower-case b)))

(sorted-set-by case-insensitive "Banana" "apple" "Cherry")
; => #{"apple" "Banana" "Cherry"}

;; Sort by string length
(sorted-map-by #(compare (count %1) (count %2))
               "hi" 1 "hello" 2 "hey" 3)
; => {"hi" 1, "hey" 3, "hello" 2}

;; Using boolean comparator
(sorted-set-by < 3 1 4 1 5 9 2 6)
; => #{1 2 3 4 5 6 9}
```

These collections support all standard collection operations (`assoc`, `dissoc`, `conj`, `disj`, `get`, `contains?`, etc.) while maintaining sort order according to the comparator.

## Notes

- All math functions return floats (`f64`), even when the result could be an integer
- Time functions return integers (`i64`)
- `setenv` is marked as unsafe internally due to Rust's thread-safety requirements, but is safe in Klujur’s single-threaded context
- `exit` does not return - it terminates the process immediately
