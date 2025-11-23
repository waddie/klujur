// klujur-core - Utility special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Utility special forms: time, eval, load-string, load-file.

use klujur_parser::KlujurVal;

use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::eval;

/// (time expr) - Time the evaluation of an expression
pub fn eval_time(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("time", "requires exactly 1 expression"));
    }

    use std::time::Instant;

    let start = Instant::now();
    let result = eval(&args[0], env)?;
    let elapsed = start.elapsed();

    // Print to stderr like Clojure
    eprintln!(
        "\"Elapsed time: {:.6} msecs\"",
        elapsed.as_secs_f64() * 1000.0
    );

    Ok(result)
}

/// (eval form) - Evaluate a form
pub fn eval_eval(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("eval", "requires exactly 1 argument"));
    }

    // First evaluate the argument to get the form to eval
    let form = eval(&args[0], env)?;

    // Then evaluate that form
    eval(&form, env)
}

/// (load-string s) - Read and evaluate all forms in string, return last result
pub fn eval_load_string(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("load-string", "requires exactly 1 argument"));
    }

    // Evaluate the argument to get the string
    let s = eval(&args[0], env)?;
    let code = match &s {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "load-string",
                "string",
                other.type_name(),
            ));
        }
    };

    // Parse and evaluate all forms
    let mut parser =
        klujur_parser::Parser::new(code).map_err(|e| Error::EvalError(format!("{:?}", e)))?;

    let mut result = KlujurVal::Nil;
    while let Some(form) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("{:?}", e)))?
    {
        result = eval(&form, env)?;
    }

    Ok(result)
}

/// (load-file path) - Load and evaluate all forms in a file, return last result
pub fn eval_load_file(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("load-file", "requires exactly 1 argument"));
    }

    // Evaluate the argument to get the path
    let path_val = eval(&args[0], env)?;
    let path = match &path_val {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "load-file",
                "string",
                other.type_name(),
            ));
        }
    };

    // Read the file contents
    let content = std::fs::read_to_string(path)
        .map_err(|e| Error::EvalError(format!("Could not read file '{}': {}", path, e)))?;

    // Parse and evaluate all forms
    let mut parser =
        klujur_parser::Parser::new(&content).map_err(|e| Error::EvalError(format!("{:?}", e)))?;

    let mut result = KlujurVal::Nil;
    while let Some(form) = parser
        .parse()
        .map_err(|e| Error::EvalError(format!("{:?}", e)))?
    {
        result = eval(&form, env)?;
    }

    Ok(result)
}
