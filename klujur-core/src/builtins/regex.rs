// klujur-core - Regular expression built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Regular expression operations using Rust regex syntax.
//!
//! Note: Klujur uses Rust's regex crate syntax, which differs from Java/Clojure:
//! - No lookahead/lookbehind (not supported by Rust regex)
//! - Named groups use `(?P<name>...)` not `(?<name>...)`
//! - Unicode categories differ (`\p{L}` vs `\p{Letter}`)
//! - Backreferences not supported in pattern matching

use klujur_parser::{KlujurRegex, KlujurVal};

use crate::error::{Error, Result};

// ============================================================================
// Regex Type Predicates
// ============================================================================

/// (regex? x) - returns true if x is a compiled regex pattern
pub(crate) fn builtin_regex_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("regex?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(&args[0], KlujurVal::Regex(_))))
}

// ============================================================================
// Regex Construction
// ============================================================================

/// (re-pattern s) - compiles string into a regex pattern
///
/// Returns a compiled regex from the given pattern string.
/// Throws an error if the pattern is invalid.
pub(crate) fn builtin_re_pattern(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("re-pattern", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::String(s) => KlujurVal::try_regex(s)
            .ok_or_else(|| Error::EvalError(format!("re-pattern: invalid regex pattern: {}", s))),
        KlujurVal::Regex(r) => Ok(KlujurVal::Regex(r.clone())),
        other => Err(Error::type_error_in(
            "re-pattern",
            "string or regex",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Regex Matching
// ============================================================================

/// (re-find pattern string) - find first match
///
/// Returns the first match of pattern in string, or nil if no match.
/// If the pattern has groups, returns a vector of [match group1 group2 ...].
/// If no groups, returns just the matched string.
pub(crate) fn builtin_re_find(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("re-find", 2, args.len()));
    }

    let regex = match &args[0] {
        KlujurVal::Regex(r) => r.clone(),
        KlujurVal::String(s) => KlujurRegex::new(s)
            .ok_or_else(|| Error::EvalError(format!("re-find: invalid regex pattern: {}", s)))?,
        other => {
            return Err(Error::type_error_in(
                "re-find",
                "regex or string",
                other.type_name(),
            ));
        }
    };

    let text = match &args[1] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("re-find", "string", other.type_name())),
    };

    // Get captures
    if let Some(caps) = regex.captures(text) {
        if caps.len() == 1 {
            // No groups, just return the match
            Ok(caps
                .get(0)
                .map(|m| KlujurVal::string(m.as_str()))
                .unwrap_or(KlujurVal::Nil))
        } else {
            // Has groups, return vector of [full-match group1 group2 ...]
            let results: Vec<KlujurVal> = caps
                .iter()
                .map(|m| {
                    m.map(|m| KlujurVal::string(m.as_str()))
                        .unwrap_or(KlujurVal::Nil)
                })
                .collect();
            Ok(KlujurVal::vector(results))
        }
    } else {
        Ok(KlujurVal::Nil)
    }
}

/// (re-matches pattern string) - match entire string
///
/// Returns the match if the entire string matches the pattern, or nil.
/// Like re-find but anchors to start and end of string.
/// If the pattern has groups, returns a vector of [match group1 group2 ...].
pub(crate) fn builtin_re_matches(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("re-matches", 2, args.len()));
    }

    let regex = match &args[0] {
        KlujurVal::Regex(r) => r.clone(),
        KlujurVal::String(s) => KlujurRegex::new(s)
            .ok_or_else(|| Error::EvalError(format!("re-matches: invalid regex pattern: {}", s)))?,
        other => {
            return Err(Error::type_error_in(
                "re-matches",
                "regex or string",
                other.type_name(),
            ));
        }
    };

    let text = match &args[1] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "re-matches",
                "string",
                other.type_name(),
            ));
        }
    };

    // Get captures
    if let Some(caps) = regex.captures(text) {
        // Check if the match spans the entire string
        if let Some(full_match) = caps.get(0)
            && full_match.start() == 0
            && full_match.end() == text.len()
        {
            if caps.len() == 1 {
                // No groups, just return the match
                return Ok(KlujurVal::string(full_match.as_str()));
            } else {
                // Has groups, return vector of [full-match group1 group2 ...]
                let results: Vec<KlujurVal> = caps
                    .iter()
                    .map(|m| {
                        m.map(|m| KlujurVal::string(m.as_str()))
                            .unwrap_or(KlujurVal::Nil)
                    })
                    .collect();
                return Ok(KlujurVal::vector(results));
            }
        }
    }
    Ok(KlujurVal::Nil)
}

/// (re-seq pattern string) - find all matches as a lazy sequence
///
/// Returns a lazy sequence of all matches of pattern in string.
/// Each element is either a string (no groups) or a vector (with groups).
///
/// Note: Currently returns an eager vector since lazy sequences require
/// the evaluator. A proper implementation would use lazy-seq.
pub(crate) fn builtin_re_seq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("re-seq", 2, args.len()));
    }

    let regex = match &args[0] {
        KlujurVal::Regex(r) => r.clone(),
        KlujurVal::String(s) => KlujurRegex::new(s)
            .ok_or_else(|| Error::EvalError(format!("re-seq: invalid regex pattern: {}", s)))?,
        other => {
            return Err(Error::type_error_in(
                "re-seq",
                "regex or string",
                other.type_name(),
            ));
        }
    };

    let text = match &args[1] {
        KlujurVal::String(s) => s.clone(),
        other => return Err(Error::type_error_in("re-seq", "string", other.type_name())),
    };

    // Collect all matches
    let has_groups = regex.regex().captures_len() > 1;
    let mut results = Vec::new();

    for caps in regex.captures_iter(&text) {
        if has_groups {
            // Has groups, return vector of [full-match group1 group2 ...]
            let match_results: Vec<KlujurVal> = caps
                .iter()
                .map(|m| {
                    m.map(|m| KlujurVal::string(m.as_str()))
                        .unwrap_or(KlujurVal::Nil)
                })
                .collect();
            results.push(KlujurVal::vector(match_results));
        } else {
            // No groups, just the matched string
            if let Some(m) = caps.get(0) {
                results.push(KlujurVal::string(m.as_str()));
            }
        }
    }

    // Return as list (Clojure's re-seq returns a lazy seq, but we return a list for now)
    Ok(KlujurVal::list(results))
}

/// (re-groups matcher) - not yet implemented
///
/// Returns groups from the most recent match. In Clojure, this operates on
/// a Matcher object. Since we don't have stateful Matchers, this is a placeholder.
pub(crate) fn builtin_re_groups(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("re-groups", 1, args.len()));
    }
    Err(Error::EvalError(
        "re-groups: not supported - use re-find with groups instead".into(),
    ))
}
