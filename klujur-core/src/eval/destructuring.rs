// klujur-core - Destructuring support
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Destructuring patterns for let bindings and function parameters.

use klujur_parser::{Keyword, KlujurVal, OrdMap, Symbol};

use crate::error::{Error, Result};

/// Result of destructuring: a list of (symbol, value) bindings
pub type Bindings = Vec<(Symbol, KlujurVal)>;

/// Destructure a binding pattern against a value, returning bindings.
/// Supports:
/// - Symbols: `x` binds directly
/// - Vectors: `[a b c]`, `[a & rest]`, `[a :as all]`
/// - Maps: `{:keys [a b]}`, `{a :a}`, `{:or {a 1}}`, `{:as m}`
pub fn destructure(pattern: &KlujurVal, value: &KlujurVal) -> Result<Bindings> {
    match pattern {
        // Simple symbol binding
        KlujurVal::Symbol(sym, _) => Ok(vec![(sym.clone(), value.clone())]),

        // Sequential destructuring
        KlujurVal::Vector(patterns, _) => {
            let patterns_vec: Vec<KlujurVal> = patterns.iter().cloned().collect();
            destructure_sequential(&patterns_vec, value)
        }

        // Associative destructuring
        KlujurVal::Map(map, _) => destructure_associative(map, value),

        other => Err(Error::syntax(
            "destructure",
            format!(
                "binding pattern must be a symbol, vector, or map, got {}",
                other.type_name()
            ),
        )),
    }
}

/// Destructure a sequential pattern (vector) against a value.
/// Supports: [a b c], [a & rest], [a :as all], [_ b c] (ignore with _)
fn destructure_sequential(patterns: &[KlujurVal], value: &KlujurVal) -> Result<Bindings> {
    let mut bindings = Vec::new();

    // Convert value to a sequence
    let items = value_to_seq(value)?;

    let mut pattern_idx = 0;
    let mut value_idx = 0;

    while pattern_idx < patterns.len() {
        let pat = &patterns[pattern_idx];

        // Check for special keywords
        if let KlujurVal::Keyword(kw) = pat
            && kw.name() == "as"
        {
            // :as binding - bind the entire value
            if pattern_idx + 1 >= patterns.len() {
                return Err(Error::syntax(
                    "destructure",
                    ":as must be followed by a symbol",
                ));
            }
            let as_sym = match &patterns[pattern_idx + 1] {
                KlujurVal::Symbol(s, _) => s.clone(),
                other => {
                    return Err(Error::syntax(
                        "destructure",
                        format!(
                            ":as must be followed by a symbol, got {}",
                            other.type_name()
                        ),
                    ));
                }
            };
            bindings.push((as_sym, value.clone()));
            pattern_idx += 2;
            continue;
        }

        // Check for & rest
        if let KlujurVal::Symbol(sym, _) = pat {
            if sym.name() == "&" {
                // Rest binding
                if pattern_idx + 1 >= patterns.len() {
                    return Err(Error::syntax(
                        "destructure",
                        "& must be followed by a binding",
                    ));
                }
                let rest_value = if value_idx < items.len() {
                    KlujurVal::list(items[value_idx..].to_vec())
                } else {
                    KlujurVal::Nil
                };
                // Recursively destructure the rest pattern
                let rest_bindings = destructure(&patterns[pattern_idx + 1], &rest_value)?;
                bindings.extend(rest_bindings);
                pattern_idx += 2;
                // Skip to end - & consumes the rest
                value_idx = items.len();
                continue;
            }

            // Ignore binding with _
            if sym.name() == "_" {
                pattern_idx += 1;
                value_idx += 1;
                continue;
            }
        }

        // Regular binding - get value at current index (or nil if out of bounds)
        let item_value = if value_idx < items.len() {
            items[value_idx].clone()
        } else {
            KlujurVal::Nil
        };

        // Recursively destructure (handles nested patterns)
        let item_bindings = destructure(pat, &item_value)?;
        bindings.extend(item_bindings);

        pattern_idx += 1;
        value_idx += 1;
    }

    Ok(bindings)
}

/// Destructure an associative pattern (map) against a value.
/// Supports: {:keys [a b]}, {:strs [a b]}, {:syms [a b]}, {a :a}, {:or {...}}, {:as m}
#[allow(clippy::mutable_key_type)]
fn destructure_associative(
    patterns: &OrdMap<KlujurVal, KlujurVal>,
    value: &KlujurVal,
) -> Result<Bindings> {
    let mut bindings = Vec::new();
    let mut defaults: Option<&OrdMap<KlujurVal, KlujurVal>> = None;

    // First pass: find :or defaults
    let or_key = KlujurVal::keyword(Keyword::new("or"));
    if let Some(or_val) = patterns.get(&or_key) {
        if let KlujurVal::Map(defaults_map, _) = or_val {
            defaults = Some(defaults_map);
        } else {
            return Err(Error::syntax(
                "destructure",
                format!(":or value must be a map, got {}", or_val.type_name()),
            ));
        }
    }

    // Get the value as a map (if it's not, we'll get nil for all lookups)
    let value_map: Option<&OrdMap<KlujurVal, KlujurVal>> = match value {
        KlujurVal::Map(m, _) => Some(m),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::syntax(
                "destructure",
                format!("cannot destructure {} as a map", other.type_name()),
            ));
        }
    };

    // Process each pattern entry
    for (pat_key, pat_val) in patterns.iter() {
        // Skip :or - already processed
        if *pat_key == or_key {
            continue;
        }

        // Check for special keywords
        if let KlujurVal::Keyword(kw) = pat_key {
            match kw.name() {
                "keys" => {
                    // {:keys [a b c]} - bind symbols to keyword lookups
                    let syms = extract_symbols(pat_val, ":keys")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::keyword(Keyword::new(sym.name()));
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "strs" => {
                    // {:strs [a b c]} - bind symbols to string lookups
                    let syms = extract_symbols(pat_val, ":strs")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::string(sym.name());
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "syms" => {
                    // {:syms [a b c]} - bind symbols to symbol lookups
                    let syms = extract_symbols(pat_val, ":syms")?;
                    for sym in syms {
                        let lookup_key = KlujurVal::symbol(Symbol::new(sym.name()));
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        bindings.push((sym, val));
                    }
                    continue;
                }
                "as" => {
                    // {:as m} - bind entire map
                    let as_sym = match pat_val {
                        KlujurVal::Symbol(s, _) => s.clone(),
                        other => {
                            return Err(Error::syntax(
                                "destructure",
                                format!(
                                    ":as must be followed by a symbol, got {}",
                                    other.type_name()
                                ),
                            ));
                        }
                    };
                    bindings.push((as_sym, value.clone()));
                    continue;
                }
                _ => {}
            }
        }

        // Regular map destructuring: {local-name lookup-key}
        // The key is the local binding, the value is what to look up
        let local_sym = match pat_key {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "destructure",
                    format!(
                        "map destructuring key must be a symbol, got {}",
                        other.type_name()
                    ),
                ));
            }
        };

        // Look up the value using pat_val as the key
        let looked_up = value_map
            .and_then(|m| m.get(pat_val).cloned())
            .unwrap_or(KlujurVal::Nil);

        // Apply defaults if nil
        let final_val = if looked_up == KlujurVal::Nil {
            defaults
                .and_then(|d| d.get(&KlujurVal::symbol(local_sym.clone())).cloned())
                .unwrap_or(KlujurVal::Nil)
        } else {
            looked_up
        };

        // Bind the symbol to the value
        bindings.push((local_sym, final_val));
    }

    Ok(bindings)
}

/// Extract symbols from a vector for :keys/:strs/:syms
fn extract_symbols(val: &KlujurVal, context: &str) -> Result<Vec<Symbol>> {
    let items = match val {
        KlujurVal::Vector(v, _) => v,
        other => {
            return Err(Error::syntax(
                "destructure",
                format!("{} requires a vector, got {}", context, other.type_name()),
            ));
        }
    };

    items
        .iter()
        .map(|item| match item {
            KlujurVal::Symbol(s, _) => Ok(s.clone()),
            other => Err(Error::syntax(
                "destructure",
                format!(
                    "{} vector must contain symbols, got {}",
                    context,
                    other.type_name()
                ),
            )),
        })
        .collect()
}

/// Look up a key in a map with fallback to defaults
fn lookup_with_default(
    key: &KlujurVal,
    value_map: Option<&OrdMap<KlujurVal, KlujurVal>>,
    defaults: Option<&OrdMap<KlujurVal, KlujurVal>>,
    sym: &Symbol,
) -> KlujurVal {
    let looked_up = value_map.and_then(|m| m.get(key).cloned());
    match looked_up {
        Some(v) if v != KlujurVal::Nil => v,
        _ => defaults
            .and_then(|d| d.get(&KlujurVal::symbol(sym.clone())).cloned())
            .unwrap_or(KlujurVal::Nil),
    }
}

/// Convert a value to a sequence (Vec) for destructuring
fn value_to_seq(value: &KlujurVal) -> Result<Vec<KlujurVal>> {
    match value {
        KlujurVal::List(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Vector(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Nil => Ok(vec![]),
        KlujurVal::String(s) => {
            // Strings destructure to characters
            Ok(s.chars().map(KlujurVal::char).collect())
        }
        other => Err(Error::syntax(
            "destructure",
            format!("cannot destructure {} as a sequence", other.type_name()),
        )),
    }
}
