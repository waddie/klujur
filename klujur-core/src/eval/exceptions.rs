// klujur-core - Exception handling
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Exception handling special forms: throw, try/catch/finally.

use klujur_parser::{KlujurVal, Symbol};

use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::eval;

/// (throw expr) - throw an exception
pub fn eval_throw(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("throw", "requires exactly 1 argument"));
    }

    let val = eval(&args[0], env)?;
    Err(Error::Thrown(val))
}

/// (try body... (catch type binding handler...)... (finally cleanup...))
/// Evaluates body forms, catches exceptions, and runs cleanup.
pub fn eval_try(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Parse body, catch clauses, and finally clause
    let mut body = Vec::new();
    let mut catch_clauses: Vec<(KlujurVal, Symbol, Vec<KlujurVal>)> = Vec::new();
    let mut finally_clause: Option<Vec<KlujurVal>> = None;

    for arg in args {
        if let KlujurVal::List(items, _) = arg
            && let Some(KlujurVal::Symbol(sym, _)) = items.front()
        {
            match sym.name() {
                "catch" => {
                    // (catch type binding handler...)
                    if items.len() < 3 {
                        return Err(Error::syntax(
                            "try",
                            "catch requires type, binding, and body",
                        ));
                    }
                    let catch_type = items[1].clone();
                    let binding = match &items[2] {
                        KlujurVal::Symbol(s, _) => s.clone(),
                        other => {
                            return Err(Error::syntax(
                                "try",
                                format!(
                                    "catch binding must be a symbol, got {}",
                                    other.type_name()
                                ),
                            ));
                        }
                    };
                    let handler: Vec<KlujurVal> = items.iter().skip(3).cloned().collect();
                    catch_clauses.push((catch_type, binding, handler));
                    continue;
                }
                "finally" => {
                    // (finally cleanup...)
                    if finally_clause.is_some() {
                        return Err(Error::syntax("try", "only one finally clause allowed"));
                    }
                    finally_clause = Some(items.iter().skip(1).cloned().collect());
                    continue;
                }
                _ => {}
            }
        }
        // Not a catch or finally - it's part of the body
        body.push(arg.clone());
    }

    // Evaluate body
    let result = eval_try_body(&body, &catch_clauses, env);

    // Always run finally, regardless of success or failure
    if let Some(finally_body) = &finally_clause {
        for expr in finally_body {
            // Evaluate finally but ignore its result (and any errors from it)
            let _ = eval(expr, env);
        }
    }

    result
}

/// Evaluate try body and handle exceptions with catch clauses
fn eval_try_body(
    body: &[KlujurVal],
    catch_clauses: &[(KlujurVal, Symbol, Vec<KlujurVal>)],
    env: &Env,
) -> Result<KlujurVal> {
    // Evaluate body - use closure to capture errors properly
    let body_result: Result<KlujurVal> = (|| {
        let mut result = KlujurVal::Nil;
        for expr in body {
            result = eval(expr, env)?;
        }
        Ok(result)
    })();

    match body_result {
        Ok(val) => Ok(val),
        Err(Error::Thrown(thrown_val)) => {
            // Try to match a catch clause
            for (catch_type, binding, handler) in catch_clauses {
                if matches_catch_type(catch_type, &thrown_val) {
                    // Create new environment with exception bound
                    let catch_env = env.child();
                    catch_env.define(binding.clone(), thrown_val.clone());

                    // Evaluate handler
                    let mut result = KlujurVal::Nil;
                    for expr in handler {
                        result = eval(expr, &catch_env)?;
                    }
                    return Ok(result);
                }
            }
            // No catch matched, re-throw
            Err(Error::Thrown(thrown_val))
        }
        Err(other_error) => {
            // Non-thrown errors (like ArityError, TypeError, etc.)
            // Convert to a thrown exception so catch can handle them
            for (catch_type, binding, handler) in catch_clauses {
                // :default catches all errors
                if matches!(catch_type, KlujurVal::Keyword(kw) if kw.name() == "default") {
                    let catch_env = env.child();
                    // Create an exception map for non-thrown errors
                    let error_val = KlujurVal::map(vec![
                        (
                            KlujurVal::Keyword(klujur_parser::Keyword::new("message")),
                            KlujurVal::string(other_error.to_string()),
                        ),
                        (
                            KlujurVal::Keyword(klujur_parser::Keyword::new("type")),
                            KlujurVal::Keyword(klujur_parser::Keyword::new("error")),
                        ),
                    ]);
                    catch_env.define(binding.clone(), error_val);

                    let mut result = KlujurVal::Nil;
                    for expr in handler {
                        result = eval(expr, &catch_env)?;
                    }
                    return Ok(result);
                }
            }
            // No catch matched, re-throw original error
            Err(other_error)
        }
    }
}

/// Check if a catch type matches the thrown value
fn matches_catch_type(catch_type: &KlujurVal, _thrown: &KlujurVal) -> bool {
    match catch_type {
        // :default catches everything
        KlujurVal::Keyword(kw) if kw.name() == "default" => true,
        // Throwable catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Throwable" => true,
        // Exception catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Exception" => true,
        // Object catches everything (Clojure compatibility)
        KlujurVal::Symbol(sym, _) if sym.name() == "Object" => true,
        // Future: support matching by :type in exception maps
        _ => false,
    }
}
