// klujur-core - String/Symbol/Keyword built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! String, symbol, and keyword operations: name, namespace, symbol, keyword, subs

use klujur_parser::{Keyword, KlujurVal, Symbol};

use crate::error::{Error, Result};

// ============================================================================
// Name and Namespace
// ============================================================================

/// (name x) - returns name part of keyword/symbol/string
pub(crate) fn builtin_name(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("name", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Keyword(kw) => Ok(KlujurVal::string(kw.name())),
        KlujurVal::Symbol(sym, _) => Ok(KlujurVal::string(sym.name())),
        KlujurVal::String(s) => Ok(KlujurVal::String(s.clone())),
        other => Err(Error::type_error_in(
            "name",
            "keyword, symbol, or string",
            other.type_name(),
        )),
    }
}

/// (namespace x) - returns namespace part of keyword/symbol, or nil
pub(crate) fn builtin_namespace(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("namespace", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Keyword(kw) => Ok(kw
            .namespace()
            .map(KlujurVal::string)
            .unwrap_or(KlujurVal::Nil)),
        KlujurVal::Symbol(sym, _) => Ok(sym
            .namespace()
            .map(KlujurVal::string)
            .unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "namespace",
            "keyword or symbol",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Symbol and Keyword Construction
// ============================================================================

/// (symbol name) or (symbol ns name) - create symbol
pub(crate) fn builtin_symbol(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => match &args[0] {
            KlujurVal::String(s) => Ok(KlujurVal::Symbol(Symbol::parse(s), None)),
            KlujurVal::Symbol(sym, _) => Ok(KlujurVal::Symbol(sym.clone(), None)),
            other => Err(Error::type_error_in("symbol", "string", other.type_name())),
        },
        2 => {
            let ns = match &args[0] {
                KlujurVal::Nil => None,
                KlujurVal::String(s) => Some(s.as_ref()),
                other => {
                    return Err(Error::type_error_in(
                        "symbol",
                        "string or nil",
                        other.type_name(),
                    ));
                }
            };
            let name = match &args[1] {
                KlujurVal::String(s) => s.as_ref(),
                other => return Err(Error::type_error_in("symbol", "string", other.type_name())),
            };
            Ok(KlujurVal::Symbol(
                match ns {
                    Some(ns) => Symbol::with_namespace(ns, name),
                    None => Symbol::new(name),
                },
                None,
            ))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("symbol".into()),
        }),
    }
}

/// (keyword name) or (keyword ns name) - create keyword
pub(crate) fn builtin_keyword(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => match &args[0] {
            KlujurVal::String(s) => Ok(KlujurVal::Keyword(Keyword::parse(s))),
            KlujurVal::Keyword(kw) => Ok(KlujurVal::Keyword(kw.clone())),
            KlujurVal::Symbol(sym, _) => {
                let kw = match sym.namespace() {
                    Some(ns) => Keyword::with_namespace(ns, sym.name()),
                    None => Keyword::new(sym.name()),
                };
                Ok(KlujurVal::Keyword(kw))
            }
            other => Err(Error::type_error_in(
                "keyword",
                "string, symbol, or keyword",
                other.type_name(),
            )),
        },
        2 => {
            let ns = match &args[0] {
                KlujurVal::Nil => None,
                KlujurVal::String(s) => Some(s.as_ref()),
                other => {
                    return Err(Error::type_error_in(
                        "keyword",
                        "string or nil",
                        other.type_name(),
                    ));
                }
            };
            let name = match &args[1] {
                KlujurVal::String(s) => s.as_ref(),
                other => return Err(Error::type_error_in("keyword", "string", other.type_name())),
            };
            Ok(KlujurVal::Keyword(match ns {
                Some(ns) => Keyword::with_namespace(ns, name),
                None => Keyword::new(name),
            }))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("keyword".into()),
        }),
    }
}

// ============================================================================
// String Operations
// ============================================================================

/// (subs s start) or (subs s start end) - substring
pub(crate) fn builtin_subs(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("subs".into()),
        });
    }

    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("subs", "string", other.type_name())),
    };

    let start = match &args[1] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => {
            return Err(Error::EvalError(
                "subs: start index must be non-negative".into(),
            ));
        }
        other => return Err(Error::type_error_in("subs", "integer", other.type_name())),
    };

    // Convert string to chars for proper Unicode handling
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();

    if start > len {
        return Err(Error::IndexOutOfBounds {
            index: start as i64,
            length: len,
        });
    }

    let end = if args.len() == 3 {
        match &args[2] {
            KlujurVal::Int(n) if *n >= 0 => (*n as usize).min(len),
            KlujurVal::Int(_) => {
                return Err(Error::EvalError(
                    "subs: end index must be non-negative".into(),
                ));
            }
            other => return Err(Error::type_error_in("subs", "integer", other.type_name())),
        }
    } else {
        len
    };

    if end < start {
        return Err(Error::EvalError(format!(
            "subs: end index {} is less than start index {}",
            end, start
        )));
    }

    let result: String = chars[start..end].iter().collect();
    Ok(KlujurVal::string(result))
}
