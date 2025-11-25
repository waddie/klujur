# Klujur

This is an LLM coded experiment. I don’t recommend actually using it. I was curious how far you can get prompting Claude Code over a weekend to build something complex.

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
# And with the bytecode VM
klj -b

# Or the unwrapped executable, if rlwrap is unavailable
klujur
klujur -b
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

### Using the Bytecode VM

Enable the bytecode compiler for improved performance:

```rust
use klujur_embed::{Engine, Result};

fn main() -> Result<()> {
    let mut engine = Engine::new()?;

    // Enable bytecode compilation mode
    engine.enable_bytecode_mode();

    // Functions are now compiled to bytecode and executed by a stack-based VM
    let result = engine.eval("((fn [x] (* x x)) 5)")?;
    println!("{}", result); // 25

    // Bytecode mode is particularly beneficial for:
    // - Recursive functions
    // - Tight loops
    // - Numerical computation
    let sum = engine.eval("(reduce + (range 10000))")?;
    println!("{}", sum); // 49995000

    Ok(())
}
```

## Intended conventions

- `.klj` extension, or `:klj` key in `.cljc` files
- `klj.edn` project files

## License

Copyright © 2025 Tom Waddington

Distributed under the MIT License. See [LICENSE file](./LICENSE) for details.
