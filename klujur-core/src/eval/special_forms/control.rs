// klujur-core - Control flow special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Control flow special forms: and, or, when, when-not, if-not, cond.

use klujur_parser::KlujurVal;

use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::eval;

/// (and exprs*) - short-circuit logical and
pub fn eval_and(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::bool(true));
    }

    let mut result = KlujurVal::bool(true);
    for expr in args {
        result = eval(expr, env)?;
        if !result.is_truthy() {
            return Ok(result);
        }
    }
    Ok(result)
}

/// (or exprs*) - short-circuit logical or
pub fn eval_or(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::Nil);
    }

    let mut result = KlujurVal::Nil;
    for expr in args {
        result = eval(expr, env)?;
        if result.is_truthy() {
            return Ok(result);
        }
    }
    // Return the last falsy value (already evaluated)
    Ok(result)
}

/// (when test body...) - execute body if test is truthy
pub fn eval_when(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("when", "requires at least a test expression"));
    }

    let test = eval(&args[0], env)?;
    if test.is_truthy() {
        let mut result = KlujurVal::Nil;
        for expr in &args[1..] {
            result = eval(expr, env)?;
        }
        Ok(result)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (when-not test body...) - execute body if test is falsy
pub fn eval_when_not(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax(
            "when-not",
            "requires at least a test expression",
        ));
    }

    let test = eval(&args[0], env)?;
    if !test.is_truthy() {
        let mut result = KlujurVal::Nil;
        for expr in &args[1..] {
            result = eval(expr, env)?;
        }
        Ok(result)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (if-not test then else?) - conditional with negated test
pub fn eval_if_not(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::syntax("if-not", "requires 2 or 3 arguments"));
    }

    let test = eval(&args[0], env)?;

    if !test.is_truthy() {
        eval(&args[1], env)
    } else if args.len() == 3 {
        eval(&args[2], env)
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (cond clauses*) - multi-way conditional
pub fn eval_cond(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if !args.len().is_multiple_of(2) {
        return Err(Error::syntax("cond", "requires even number of forms"));
    }

    for pair in args.chunks(2) {
        let test = &pair[0];

        // Check for :else keyword
        let is_else = matches!(test, KlujurVal::Keyword(kw) if kw.name() == "else");

        let test_result = if is_else {
            KlujurVal::bool(true)
        } else {
            eval(test, env)?
        };

        if test_result.is_truthy() {
            return eval(&pair[1], env);
        }
    }

    Ok(KlujurVal::Nil)
}
