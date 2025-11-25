// klujur-core - String/Symbol/Keyword built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! String, symbol, and keyword operations: name, namespace, symbol, keyword, subs

use klujur_parser::{Keyword, KlujurVal, Symbol};

use crate::error::{AritySpec, Error, Result};

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

// ============================================================================
// Case Conversion
// ============================================================================

/// (upper-case s) - converts string to uppercase
pub(crate) fn builtin_upper_case(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("upper-case", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => Ok(KlujurVal::string(s.to_uppercase())),
        other => Err(Error::type_error_in(
            "upper-case",
            "string",
            other.type_name(),
        )),
    }
}

/// (lower-case s) - converts string to lowercase
pub(crate) fn builtin_lower_case(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("lower-case", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => Ok(KlujurVal::string(s.to_lowercase())),
        other => Err(Error::type_error_in(
            "lower-case",
            "string",
            other.type_name(),
        )),
    }
}

/// (capitalize s) - capitalizes first character, lowercases the rest
pub(crate) fn builtin_capitalize(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("capitalize", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => {
            let s = s.as_ref();
            if s.is_empty() {
                return Ok(KlujurVal::string(""));
            }
            let mut chars = s.chars();
            let first = chars.next().unwrap().to_uppercase().to_string();
            let rest: String = chars.collect::<String>().to_lowercase();
            Ok(KlujurVal::string(first + &rest))
        }
        other => Err(Error::type_error_in(
            "capitalize",
            "string",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Trimming
// ============================================================================

/// (trim s) - removes leading and trailing whitespace
pub(crate) fn builtin_trim(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("trim", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => Ok(KlujurVal::string(s.trim())),
        other => Err(Error::type_error_in("trim", "string", other.type_name())),
    }
}

/// (triml s) - removes leading whitespace
pub(crate) fn builtin_triml(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("triml", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => Ok(KlujurVal::string(s.trim_start())),
        other => Err(Error::type_error_in("triml", "string", other.type_name())),
    }
}

/// (trimr s) - removes trailing whitespace
pub(crate) fn builtin_trimr(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("trimr", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::String(s) => Ok(KlujurVal::string(s.trim_end())),
        other => Err(Error::type_error_in("trimr", "string", other.type_name())),
    }
}

// ============================================================================
// Split and Join
// ============================================================================

/// (split s delimiter) - splits string by delimiter, returns vector
pub(crate) fn builtin_split(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("split", 2, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("split", "string", other.type_name())),
    };
    let delimiter = match &args[1] {
        KlujurVal::String(d) => d.as_ref(),
        other => return Err(Error::type_error_in("split", "string", other.type_name())),
    };
    let parts: Vec<KlujurVal> = s.split(delimiter).map(KlujurVal::string).collect();
    Ok(KlujurVal::vector(parts))
}

/// (join coll) or (join sep coll) - joins collection elements into string
pub(crate) fn builtin_join(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (join coll) - join with empty separator
            let items = super::to_seq(&args[0])?;
            let parts: Vec<String> = items
                .iter()
                .map(|v| match v {
                    KlujurVal::String(s) => s.to_string(),
                    KlujurVal::Char(c) => c.to_string(),
                    KlujurVal::Nil => String::new(),
                    other => format!("{}", other),
                })
                .collect();
            Ok(KlujurVal::string(parts.join("")))
        }
        2 => {
            // (join sep coll) - join with separator
            let sep = match &args[0] {
                KlujurVal::String(s) => s.as_ref().to_string(),
                KlujurVal::Char(c) => c.to_string(),
                other => return Err(Error::type_error_in("join", "string", other.type_name())),
            };
            let items = super::to_seq(&args[1])?;
            let parts: Vec<String> = items
                .iter()
                .map(|v| match v {
                    KlujurVal::String(s) => s.to_string(),
                    KlujurVal::Char(c) => c.to_string(),
                    KlujurVal::Nil => String::new(),
                    other => format!("{}", other),
                })
                .collect();
            Ok(KlujurVal::string(parts.join(&sep)))
        }
        _ => Err(Error::ArityError {
            expected: AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("join".into()),
        }),
    }
}

// ============================================================================
// Replace
// ============================================================================

/// (replace s match replacement) - replaces all occurrences
pub(crate) fn builtin_replace(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("replace", 3, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("replace", "string", other.type_name())),
    };
    let pattern = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => return Err(Error::type_error_in("replace", "string", other.type_name())),
    };
    let replacement = match &args[2] {
        KlujurVal::String(r) => r.as_ref(),
        other => return Err(Error::type_error_in("replace", "string", other.type_name())),
    };
    Ok(KlujurVal::string(s.replace(pattern, replacement)))
}

/// (replace-first s match replacement) - replaces first occurrence only
pub(crate) fn builtin_replace_first(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("replace-first", 3, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "replace-first",
                "string",
                other.type_name(),
            ));
        }
    };
    let pattern = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "replace-first",
                "string",
                other.type_name(),
            ));
        }
    };
    let replacement = match &args[2] {
        KlujurVal::String(r) => r.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "replace-first",
                "string",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::string(s.replacen(pattern, replacement, 1)))
}

// ============================================================================
// String Predicates
// ============================================================================

/// (blank? s) - true if s is nil, empty, or whitespace only
pub(crate) fn builtin_blank_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("blank?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::bool(true)),
        KlujurVal::String(s) => Ok(KlujurVal::bool(s.trim().is_empty())),
        other => Err(Error::type_error_in(
            "blank?",
            "string or nil",
            other.type_name(),
        )),
    }
}

/// (starts-with? s substr) - true if s starts with substr
pub(crate) fn builtin_starts_with_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("starts-with?", 2, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "starts-with?",
                "string",
                other.type_name(),
            ));
        }
    };
    let substr = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "starts-with?",
                "string",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::bool(s.starts_with(substr)))
}

/// (ends-with? s substr) - true if s ends with substr
pub(crate) fn builtin_ends_with_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("ends-with?", 2, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "ends-with?",
                "string",
                other.type_name(),
            ));
        }
    };
    let substr = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "ends-with?",
                "string",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::bool(s.ends_with(substr)))
}

/// (includes? s substr) - true if s contains substr
pub(crate) fn builtin_includes_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("includes?", 2, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "includes?",
                "string",
                other.type_name(),
            ));
        }
    };
    let substr = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "includes?",
                "string",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::bool(s.contains(substr)))
}

// ============================================================================
// Search and Escape
// ============================================================================

/// (index-of s substr) or (index-of s substr from) - returns index of substr, or nil
pub(crate) fn builtin_index_of(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("index-of".into()),
        });
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "index-of",
                "string",
                other.type_name(),
            ));
        }
    };
    let substr = match &args[1] {
        KlujurVal::String(p) => p.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "index-of",
                "string",
                other.type_name(),
            ));
        }
    };

    // Convert to chars for proper Unicode handling
    let chars: Vec<char> = s.chars().collect();
    let substr_chars: Vec<char> = substr.chars().collect();

    let from_idx = if args.len() == 3 {
        match &args[2] {
            KlujurVal::Int(n) if *n >= 0 => *n as usize,
            KlujurVal::Int(_) => {
                return Err(Error::EvalError(
                    "index-of: from-index must be non-negative".into(),
                ));
            }
            other => {
                return Err(Error::type_error_in(
                    "index-of",
                    "integer",
                    other.type_name(),
                ));
            }
        }
    } else {
        0
    };

    if from_idx > chars.len() {
        return Ok(KlujurVal::Nil);
    }

    // Search for substr starting from from_idx
    if substr_chars.is_empty() {
        return Ok(KlujurVal::int(from_idx as i64));
    }

    for i in from_idx..=chars.len().saturating_sub(substr_chars.len()) {
        if chars[i..i + substr_chars.len()] == substr_chars[..] {
            return Ok(KlujurVal::int(i as i64));
        }
    }

    Ok(KlujurVal::Nil)
}

/// (escape s cmap) - replaces chars in s according to char-map
pub(crate) fn builtin_escape(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("escape", 2, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("escape", "string", other.type_name())),
    };
    let cmap = match &args[1] {
        KlujurVal::Map(m, _) => m,
        other => return Err(Error::type_error_in("escape", "map", other.type_name())),
    };

    let mut result = String::new();
    for c in s.chars() {
        let char_key = KlujurVal::char(c);
        if let Some(replacement) = cmap.get(&char_key) {
            match replacement {
                KlujurVal::String(r) => result.push_str(r),
                KlujurVal::Char(r) => result.push(*r),
                other => result.push_str(&format!("{}", other)),
            }
        } else {
            result.push(c);
        }
    }
    Ok(KlujurVal::string(result))
}
