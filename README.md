# Klujur

Klujur is an interpreted programming language modelled closely after [Clojure](https://github.com/clojure/clojure). Klujur is written in Rust and intended to be useful as an embedded scripting language, but also ships with a standalone CLI REPL.

## Installation

```sh
cargo xtask install
```

`cargo` will build and install the `klujur` executable, defaulting to `~/.cargo/bin`.

## Use

```sh
# Run the rlwrap wrapper
klj

# Or the unwrapped executable, if rlwrap is unavailable
klujur
```

## Intended conventions

- `.klj` extension, or `:klj` key in `.cljc` files
- `klj.edn` project files

## License

Copyright © 2025 Tom Waddington

Distributed under the MIT License. See LICENSE file for details.
