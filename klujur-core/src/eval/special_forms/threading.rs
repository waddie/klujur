// klujur-core - Threading macros
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Threading special forms: ->, ->>, as->.

use klujur_parser::KlujurVal;

use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::eval;

/// (-> x forms...) - thread first: insert x as second item in each form
pub fn eval_thread_first(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("->", "requires at least one argument"));
    }

    let mut result = eval(&args[0], env)?;

    for form in &args[1..] {
        result = match form {
            KlujurVal::List(items, _) if !items.is_empty() => {
                // Insert result as second argument: (f a b) -> (f result a b)
                let mut new_list = vec![items[0].clone(), result];
                new_list.extend(items.iter().skip(1).cloned());
                eval(&KlujurVal::list(new_list), env)?
            }
            KlujurVal::Symbol(_, _) | KlujurVal::Keyword(_) => {
                // Symbol or keyword: treat as (f result)
                // Keywords can be used as functions to look up values in maps
                let call = KlujurVal::list(vec![form.clone(), result]);
                eval(&call, env)?
            }
            other => {
                return Err(Error::syntax(
                    "->",
                    format!(
                        "form must be a list, symbol, or keyword, got {}",
                        other.type_name()
                    ),
                ));
            }
        };
    }

    Ok(result)
}

/// (->> x forms...) - thread last: insert x as last item in each form
pub fn eval_thread_last(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("->>", "requires at least one argument"));
    }

    let mut result = eval(&args[0], env)?;

    for form in &args[1..] {
        result = match form {
            KlujurVal::List(items, _) if !items.is_empty() => {
                // Insert result as last argument: (f a b) -> (f a b result)
                let mut new_list: Vec<KlujurVal> = items.iter().cloned().collect();
                new_list.push(result);
                eval(&KlujurVal::list(new_list), env)?
            }
            KlujurVal::Symbol(_, _) | KlujurVal::Keyword(_) => {
                // Symbol or keyword: treat as (f result)
                // Keywords can be used as functions to look up values in maps
                let call = KlujurVal::list(vec![form.clone(), result]);
                eval(&call, env)?
            }
            other => {
                return Err(Error::syntax(
                    "->>",
                    format!(
                        "form must be a list, symbol, or keyword, got {}",
                        other.type_name()
                    ),
                ));
            }
        };
    }

    Ok(result)
}

/// (as-> expr name forms...) - thread with named binding
pub fn eval_as_thread(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::syntax(
            "as->",
            "requires expression, name, and forms",
        ));
    }

    let name = match &args[1] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "as->",
                format!(
                    "second argument must be a symbol, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let mut result = eval(&args[0], env)?;

    // Create a child environment for the binding
    let thread_env = env.child();

    for form in &args[2..] {
        thread_env.define(name.clone(), result);
        result = eval(form, &thread_env)?;
    }

    Ok(result)
}
