# Klujur

Klujur is an interpreted programming language modelled on [Clojure](https://github.com/clojure/clojure). Klujur is written in Rust and intended to be useful as an embedded scripting language, but also ships with a standalone CLI REPL.

## Installation

```sh
cargo xtask install
```

`cargo` will build and install the `klujur` executable, defaulting to `~/.cargo/bin`.

## Use

```sh
# Run with rlwrap wrapper
klj

# Or the unwrapped executable, if rlwrap is unavailable
klujur
```

## Embedding

Add `klujur-embed` to your `Cargo.toml`:

```toml
[dependencies]
klujur-embed = { git = "https://github.com/waddie/klujur" }
```

```rust
use klujur_embed::{Engine, KlujurVal, Result};

fn main() -> Result<()> {
    let mut engine = Engine::new()?;

    // Evaluate code
    let result = engine.eval("(+ 1 2 3)")?;
    println!("{}", result); // 6

    // Register native functions
    engine.register_native("greet", |args: &[KlujurVal]| {
        let name = match args.first() {
            Some(KlujurVal::String(s)) => s.as_ref(),
            _ => "World",
        };
        Ok(KlujurVal::string(format!("hello, {}!", name)))
    });

    engine.eval("(println (greet \"Klujur\"))")?; // hello, Klujur!
    Ok(())
}
```

## Intended conventions

- `.klj` extension, or `:klj` key in `.cljc` files
- `klj.edn` project files

## License

Copyright © 2025 Tom Waddington

Distributed under the MIT License. See [LICENSE file](./LICENSE) for details.
