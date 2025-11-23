// klujur-embed - Engine implementation
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! The Engine struct - main entry point for embedding Klujur.

use std::path::Path;

use klujur_core::{
    Env, Error, Namespace, Result, Symbol, eval, init_stdlib, make_native_fn, register_builtins,
    set_max_eval_depth,
};
use klujur_parser::{KlujurVal, Parser};

use crate::convert::{FromKlujurVal, IntoKlujurVal};

/// The Klujur scripting engine.
///
/// `Engine` provides a high-level interface for evaluating Klujur code,
/// registering Rust functions, and interacting with Klujur values.
///
/// # Example
///
/// ```rust
/// use klujur_embed::Engine;
///
/// let engine = Engine::new().unwrap();
/// let result = engine.eval("(+ 1 2 3)").unwrap();
/// assert_eq!(result.to_string(), "6");
/// ```
pub struct Engine {
    env: Env,
}

impl Engine {
    /// Create a new Engine with the standard library loaded.
    pub fn new() -> Result<Self> {
        let env = Env::new();
        register_builtins(&env);
        init_stdlib(&env)?;
        Ok(Engine { env })
    }

    /// Create a new Engine without the standard library.
    ///
    /// Useful for sandboxed environments or when you want to provide
    /// your own functions.
    pub fn new_bare() -> Self {
        let env = Env::new();
        register_builtins(&env);
        Engine { env }
    }

    /// Set the maximum recursion depth for evaluation.
    ///
    /// Default is 10,000. Setting this lower can help catch runaway recursion.
    /// Returns the previous value.
    pub fn set_max_depth(&mut self, depth: usize) -> usize {
        set_max_eval_depth(depth)
    }

    /// Evaluate a string of Klujur code.
    ///
    /// Returns the result of the last expression.
    ///
    /// # Example
    ///
    /// ```rust
    /// use klujur_embed::Engine;
    ///
    /// let engine = Engine::new().unwrap();
    /// let result = engine.eval("(def x 42) (* x 2)").unwrap();
    /// assert_eq!(result.to_string(), "84");
    /// ```
    pub fn eval(&self, code: &str) -> Result<KlujurVal> {
        let mut parser =
            Parser::new(code).map_err(|e| Error::EvalError(format!("Parse error: {:?}", e)))?;

        let mut result = KlujurVal::Nil;
        while let Some(expr) = parser
            .parse()
            .map_err(|e| Error::EvalError(format!("Parse error: {:?}", e)))?
        {
            result = eval(&expr, &self.env)?;
        }
        Ok(result)
    }

    /// Evaluate a file of Klujur code.
    ///
    /// Returns the result of the last expression.
    pub fn eval_file(&self, path: impl AsRef<Path>) -> Result<KlujurVal> {
        let code = std::fs::read_to_string(path.as_ref())
            .map_err(|e| Error::io("eval_file", Some(path.as_ref().display().to_string()), e))?;
        self.eval(&code)
    }

    /// Get a value from the current namespace.
    ///
    /// Returns `None` if the symbol is not defined.
    pub fn get(&self, name: &str) -> Option<KlujurVal> {
        let registry = self.env.registry();
        let current_ns = registry.current();
        let sym = Symbol::new(name);
        current_ns.resolve(&sym).map(|var| var.deref())
    }

    /// Get a typed value from the current namespace.
    ///
    /// Returns `None` if the symbol is not defined or cannot be converted.
    pub fn get_as<T: FromKlujurVal>(&self, name: &str) -> Option<T> {
        self.get(name).and_then(|v| T::from_klujur_val(&v).ok())
    }

    /// Set a value in the current namespace.
    pub fn set(&self, name: &str, value: impl IntoKlujurVal) {
        let registry = self.env.registry();
        let current_ns = registry.current();
        let klj_val = value.into_klujur_val();
        current_ns.intern_with_value(name, klj_val);
    }

    /// Call a function by name with arguments.
    ///
    /// # Example
    ///
    /// ```rust
    /// use klujur_embed::{Engine, KlujurVal};
    ///
    /// let engine = Engine::new().unwrap();
    /// let result = engine.call("+", &[
    ///     KlujurVal::int(1),
    ///     KlujurVal::int(2),
    ///     KlujurVal::int(3),
    /// ]).unwrap();
    /// assert_eq!(result.to_string(), "6");
    /// ```
    pub fn call(&self, name: &str, args: &[KlujurVal]) -> Result<KlujurVal> {
        let func = self
            .get(name)
            .ok_or_else(|| Error::UndefinedSymbol(Symbol::new(name)))?;
        klujur_core::apply(&func, args)
    }

    /// Register a native Rust function.
    ///
    /// The function must take a slice of `KlujurVal` and return a `Result<KlujurVal>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use klujur_embed::{Engine, KlujurVal, Result};
    ///
    /// let mut engine = Engine::new().unwrap();
    /// engine.register_native("greet", |args| {
    ///     let name = match args.first() {
    ///         Some(KlujurVal::String(s)) => s.as_ref(),
    ///         _ => "World",
    ///     };
    ///     Ok(KlujurVal::string(format!("Hello, {}!", name)))
    /// });
    /// ```
    pub fn register_native(
        &mut self,
        name: &str,
        func: impl Fn(&[KlujurVal]) -> Result<KlujurVal> + 'static,
    ) {
        let registry = self.env.registry();
        let current_ns = registry.current();
        let native_fn = make_native_fn(name.to_string(), func);
        current_ns.intern_with_value(name, KlujurVal::NativeFn(native_fn));
    }

    /// Register a native function into the klujur.core namespace.
    ///
    /// This makes the function available to all code without requiring
    /// an explicit namespace prefix.
    pub fn register_native_core(
        &mut self,
        name: &str,
        func: impl Fn(&[KlujurVal]) -> Result<KlujurVal> + 'static,
    ) {
        let registry = self.env.registry();
        let core_ns = registry.find_or_create("klujur.core");
        let native_fn = make_native_fn(name.to_string(), func);
        core_ns.intern_with_value(name, KlujurVal::NativeFn(native_fn));
    }

    /// Get access to the underlying environment.
    ///
    /// This is useful for advanced use cases where you need direct
    /// access to the Klujur runtime.
    pub fn env(&self) -> &Env {
        &self.env
    }

    /// Get the current namespace.
    pub fn current_namespace(&self) -> Namespace {
        self.env.registry().current()
    }

    /// Switch to a different namespace.
    pub fn set_namespace(&self, name: &str) {
        self.env.registry().set_current(name);
    }
}

impl Default for Engine {
    fn default() -> Self {
        Self::new().expect("Failed to create default Engine")
    }
}
