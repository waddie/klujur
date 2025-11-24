// klujur-core - Destructuring support
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Destructuring patterns for let bindings and function parameters.

use klujur_parser::{Keyword, KlujurVal, OrdMap, Symbol};

use crate::error::{Error, Result};

/// Result of destructuring: a list of (symbol, value) bindings
pub type Bindings = Vec<(Symbol, KlujurVal)>;

/// Maximum nesting depth for destructuring patterns to prevent stack overflow.
///
/// 100 levels of nesting is far beyond any reasonable use case (most real-world
/// patterns are 2-3 levels deep). This limit exists to catch pathological
/// inputs or infinite loops in pattern expansion, not to restrict legitimate usage.
///
/// This is not currently configurable as the limit is generous enough for all
/// practical purposes. If needed, this could be made configurable via a thread-local
/// similar to `MAX_EVAL_DEPTH`.
const MAX_DESTRUCTURE_DEPTH: usize = 100;

/// Destructure a binding pattern against a value, returning bindings.
/// Supports:
/// - Symbols: `x` binds directly
/// - Vectors: `[a b c]`, `[a & rest]`, `[a :as all]`
/// - Maps: `{:keys [a b]}`, `{a :a}`, `{:or {a 1}}`, `{:as m}`
#[must_use = "destructuring result should be used to create bindings"]
pub fn destructure(pattern: &KlujurVal, value: &KlujurVal) -> Result<Bindings> {
    destructure_with_depth(pattern, value, 0)
}

/// Internal destructuring with depth tracking to prevent stack overflow
fn destructure_with_depth(
    pattern: &KlujurVal,
    value: &KlujurVal,
    depth: usize,
) -> Result<Bindings> {
    if depth > MAX_DESTRUCTURE_DEPTH {
        return Err(Error::EvalError(format!(
            "destructuring pattern too deeply nested (max {} levels)",
            MAX_DESTRUCTURE_DEPTH
        )));
    }

    match pattern {
        // Simple symbol binding
        KlujurVal::Symbol(sym, _) => Ok(vec![(sym.clone(), value.clone())]),

        // Sequential destructuring
        KlujurVal::Vector(patterns, _) => {
            let patterns_vec: Vec<KlujurVal> = patterns.iter().cloned().collect();
            destructure_sequential(&patterns_vec, value, depth)
        }

        // Associative destructuring
        KlujurVal::Map(map, _) => destructure_associative(map, value, depth),

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
fn destructure_sequential(
    patterns: &[KlujurVal],
    value: &KlujurVal,
    depth: usize,
) -> Result<Bindings> {
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
                let rest_bindings =
                    destructure_with_depth(&patterns[pattern_idx + 1], &rest_value, depth + 1)?;
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
        let item_bindings = destructure_with_depth(pat, &item_value, depth + 1)?;
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
    depth: usize,
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
                    // {:ns/keys [a b c]} - bind symbols to namespaced keyword lookups
                    // {:keys [ns/a ns/b]} - bind symbols to their namespaced keyword lookups
                    let syms = extract_symbols(pat_val, ":keys")?;
                    let kw_namespace = kw.namespace(); // e.g., "user" from :user/keys
                    for sym in syms {
                        // Determine the lookup key namespace:
                        // 1. If symbol has a namespace (e.g., user/name), use that
                        // 2. Else if :ns/keys was used (e.g., :user/keys), use that namespace
                        // 3. Else no namespace
                        let lookup_key = if let Some(sym_ns) = sym.namespace() {
                            // Symbol has explicit namespace: {:keys [user/name]} -> :user/name
                            KlujurVal::keyword(Keyword::with_namespace(sym_ns, sym.name()))
                        } else if let Some(key_ns) = kw_namespace {
                            // :ns/keys shorthand: {:user/keys [name]} -> :user/name
                            KlujurVal::keyword(Keyword::with_namespace(key_ns, sym.name()))
                        } else {
                            // No namespace: {:keys [name]} -> :name
                            KlujurVal::keyword(Keyword::new(sym.name()))
                        };
                        let val = lookup_with_default(&lookup_key, value_map, defaults, &sym);
                        // Bind to local name (without namespace)
                        let local_sym = Symbol::new(sym.name());
                        bindings.push((local_sym, val));
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

        // Regular map destructuring: {local-binding lookup-key}
        // The key is the binding pattern, the value is what to look up
        // Supports:
        //   {local-sym :key}      - simple symbol binding
        //   {[a b] :pair}         - vector destructuring pattern
        //   {{:keys [x]} :nested} - nested map destructuring pattern
        match pat_key {
            KlujurVal::Symbol(local_sym, _) => {
                // Simple symbol binding
                // Look up the value using pat_val as the key
                // Defaults only apply when key is MISSING, not when value is nil
                let final_val = if let Some(m) = value_map {
                    if m.contains_key(pat_val) {
                        // Key exists - use its value (even if nil)
                        m.get(pat_val).cloned().unwrap_or(KlujurVal::Nil)
                    } else {
                        // Key missing - apply default
                        defaults
                            .and_then(|d| d.get(&KlujurVal::symbol(local_sym.clone())).cloned())
                            .unwrap_or(KlujurVal::Nil)
                    }
                } else {
                    // No map - apply default
                    defaults
                        .and_then(|d| d.get(&KlujurVal::symbol(local_sym.clone())).cloned())
                        .unwrap_or(KlujurVal::Nil)
                };
                bindings.push((local_sym.clone(), final_val));
            }
            KlujurVal::Vector(_, _) | KlujurVal::Map(_, _) => {
                // Nested destructuring pattern (vector or map)
                // Look up the value using pat_val as the key, then recursively destructure
                let looked_up = value_map
                    .and_then(|m| m.get(pat_val).cloned())
                    .unwrap_or(KlujurVal::Nil);
                // Recursively destructure the nested pattern
                let nested_bindings = destructure_with_depth(pat_key, &looked_up, depth + 1)?;
                bindings.extend(nested_bindings);
            }
            other => {
                return Err(Error::syntax(
                    "destructure",
                    format!(
                        "map destructuring key must be a symbol, vector, or map pattern, got {}",
                        other.type_name()
                    ),
                ));
            }
        }
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

/// Look up a key in a map with fallback to defaults.
/// Defaults only apply when the key is MISSING from the map, not when the value is nil.
fn lookup_with_default(
    key: &KlujurVal,
    value_map: Option<&OrdMap<KlujurVal, KlujurVal>>,
    defaults: Option<&OrdMap<KlujurVal, KlujurVal>>,
    sym: &Symbol,
) -> KlujurVal {
    // Check if key exists in the map (not just if value is non-nil)
    if let Some(m) = value_map
        && m.contains_key(key)
    {
        // Key exists - return its value (even if nil)
        return m.get(key).cloned().unwrap_or(KlujurVal::Nil);
    }
    // Key missing - apply default if available
    defaults
        .and_then(|d| d.get(&KlujurVal::symbol(sym.clone())).cloned())
        .unwrap_or(KlujurVal::Nil)
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
