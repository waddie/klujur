// klujur-core - Namespace special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Namespace special forms: in-ns, var, ns-publics, ns-interns, refer, alias, require, use, all-ns, find-ns, create-ns, remove-ns, the-ns, ns-name

use klujur_parser::{KlujurVal, Symbol};

use crate::env::Env;
use crate::error::{Error, Result};

use super::{eval, lookup_symbol};

// ============================================================================
// Namespace Special Forms
// ============================================================================

/// (in-ns ns-sym) - Switch to the given namespace (creating if needed)
pub(crate) fn eval_in_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("in-ns", "requires exactly 1 argument"));
    }

    // in-ns evaluates its argument (unlike ns which is typically a macro)
    let arg = eval(&args[0], env)?;

    let name = match arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::syntax(
                "in-ns",
                format!(
                    "argument must be a symbol or string, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let registry = env.registry();
    let ns = registry.set_current(name);

    // Return the namespace name as a symbol
    Ok(KlujurVal::symbol(Symbol::new(&ns.name())))
}

/// (var sym) - get the Var itself (not its value)
pub(crate) fn eval_var(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("var", "requires exactly 1 argument"));
    }

    let sym = match &args[0] {
        KlujurVal::Symbol(s, _) => s,
        other => {
            return Err(Error::syntax(
                "var",
                format!("argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    // Look up the symbol (check both lexical env and namespace)
    let val = lookup_symbol(sym, env)?;

    // Return the Var if it is one, otherwise error
    match val {
        KlujurVal::Var(_) => Ok(val),
        _ => Err(Error::syntax(
            "var",
            format!("symbol '{}' is not bound to a Var", sym),
        )),
    }
}

/// Helper to get a namespace from an evaluated argument (symbol or string).
fn get_namespace_from_arg(
    arg: &KlujurVal,
    env: &Env,
    fn_name: &str,
) -> Result<crate::namespace::Namespace> {
    let ns_name = match arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::EvalError(format!(
                "{}: argument must be a symbol or string, got {}",
                fn_name,
                other.type_name()
            )));
        }
    };

    let registry = env.registry();
    registry
        .find(&ns_name)
        .ok_or_else(|| Error::namespace_not_found(&ns_name))
}

/// (ns-publics ns) - returns a map of symbols to public vars in namespace
pub(crate) fn eval_ns_publics(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-publics", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns = get_namespace_from_arg(&arg, env, "ns-publics")?;

    // Get public vars and convert to map of symbol -> var
    let publics = ns.publics();
    let pairs: Vec<(KlujurVal, KlujurVal)> = publics
        .into_iter()
        .map(|(name, var)| (KlujurVal::symbol(Symbol::new(&name)), KlujurVal::Var(var)))
        .collect();

    Ok(KlujurVal::map(pairs))
}

/// (ns-interns ns) - returns a map of symbols to all vars in namespace
pub(crate) fn eval_ns_interns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-interns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns = get_namespace_from_arg(&arg, env, "ns-interns")?;

    // Get all interned vars and convert to map of symbol -> var
    let interns = ns.interns();
    let pairs: Vec<(KlujurVal, KlujurVal)> = interns
        .into_iter()
        .map(|(name, var)| (KlujurVal::symbol(Symbol::new(&name)), KlujurVal::Var(var)))
        .collect();

    Ok(KlujurVal::map(pairs))
}

/// (refer ns-sym & filters) - refer vars from another namespace
///
/// Refers public vars from the specified namespace into the current namespace.
/// Private vars cannot be referred and will cause an error.
///
/// Basic usage: (refer 'other.ns)
/// With filters: (refer 'other.ns :only [foo bar])
///              (refer 'other.ns :exclude [baz])
///              (refer 'other.ns :rename {foo bar})
pub(crate) fn eval_refer(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("refer", "requires at least 1 argument"));
    }

    // Evaluate the namespace argument
    let ns_arg = eval(&args[0], env)?;
    let source_ns = get_namespace_from_arg(&ns_arg, env, "refer")?;

    let registry = env.registry();
    let current_ns = registry.current();

    // Parse filter options
    let mut only: Option<Vec<String>> = None;
    let mut exclude: Vec<String> = Vec::new();
    let mut rename: std::collections::HashMap<String, String> = std::collections::HashMap::new();

    let mut i = 1;
    while i < args.len() {
        let filter_key = eval(&args[i], env)?;
        match &filter_key {
            KlujurVal::Keyword(kw) if kw.name() == "only" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax("refer", ":only requires a vector argument"));
                }
                // Don't evaluate - use unevaluated symbols directly
                if let KlujurVal::Vector(items, _) = &args[i + 1] {
                    only = Some(
                        items
                            .iter()
                            .filter_map(|v| match v {
                                KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                _ => None,
                            })
                            .collect(),
                    );
                } else {
                    return Err(Error::syntax("refer", ":only requires a vector argument"));
                }
                i += 2;
            }
            KlujurVal::Keyword(kw) if kw.name() == "exclude" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax(
                        "refer",
                        ":exclude requires a vector argument",
                    ));
                }
                // Don't evaluate - use unevaluated symbols directly
                if let KlujurVal::Vector(items, _) = &args[i + 1] {
                    exclude = items
                        .iter()
                        .filter_map(|v| match v {
                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                            _ => None,
                        })
                        .collect();
                } else {
                    return Err(Error::syntax(
                        "refer",
                        ":exclude requires a vector argument",
                    ));
                }
                i += 2;
            }
            KlujurVal::Keyword(kw) if kw.name() == "rename" => {
                if i + 1 >= args.len() {
                    return Err(Error::syntax("refer", ":rename requires a map argument"));
                }
                // Don't evaluate - use unevaluated map directly
                if let KlujurVal::Map(map, _) = &args[i + 1] {
                    for (k, v) in map.iter() {
                        if let (KlujurVal::Symbol(ks, _), KlujurVal::Symbol(vs, _)) = (k, v) {
                            rename.insert(ks.name().to_string(), vs.name().to_string());
                        }
                    }
                } else {
                    return Err(Error::syntax("refer", ":rename requires a map argument"));
                }
                i += 2;
            }
            _ => {
                return Err(Error::syntax(
                    "refer",
                    format!("unknown filter option: {}", filter_key),
                ));
            }
        }
    }

    // Get public vars from source namespace
    let publics = source_ns.publics();

    // Determine which vars to refer
    let vars_to_refer: Vec<(String, _)> = match only {
        Some(only_list) => {
            // Only refer specified vars
            only_list
                .into_iter()
                .filter_map(|name| {
                    if exclude.contains(&name) {
                        return None;
                    }
                    if let Some(var) = publics.get(&name) {
                        let refer_name = rename.get(&name).cloned().unwrap_or(name);
                        Some((refer_name, var.clone()))
                    } else {
                        // Check if it exists but is private
                        if source_ns.interns().contains_key(&name) {
                            // Var exists but is private - this is an error
                            None // Will be handled below
                        } else {
                            None
                        }
                    }
                })
                .collect()
        }
        None => {
            // Refer all public vars
            publics
                .into_iter()
                .filter(|(name, _)| !exclude.contains(name))
                .map(|(name, var)| {
                    let refer_name = rename.get(&name).cloned().unwrap_or(name);
                    (refer_name, var)
                })
                .collect()
        }
    };

    // Check for private var access attempts in :only
    if let Some(ref only_list) = args.get(2).and_then(|_| {
        // Re-parse only list for error checking
        let mut i = 1;
        while i < args.len() {
            if let Ok(KlujurVal::Keyword(kw)) = eval(&args[i], env)
                && kw.name() == "only"
                && i + 1 < args.len()
                && let Ok(KlujurVal::Vector(items, _)) = eval(&args[i + 1], env)
            {
                return Some(
                    items
                        .iter()
                        .filter_map(|v| match v {
                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                );
            }
            i += 1;
        }
        None
    }) {
        let all_interns = source_ns.interns();
        let public_names: std::collections::HashSet<_> =
            source_ns.publics().keys().cloned().collect();

        for name in only_list {
            if all_interns.contains_key(name) && !public_names.contains(name) {
                return Err(Error::not_public(name, source_ns.name()));
            }
        }
    }

    // Add refers to current namespace
    for (name, var) in vars_to_refer {
        current_ns.refer(name, var);
    }

    Ok(KlujurVal::Nil)
}

/// (alias alias-sym ns-sym) - Add an alias in the current namespace
///
/// Creates an alias so that `alias-sym/foo` resolves to `ns-sym/foo`.
/// Example: (alias 's 'clojure.string)
pub(crate) fn eval_alias(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::syntax("alias", "requires exactly 2 arguments"));
    }

    // Get alias symbol
    let alias_val = eval(&args[0], env)?;
    let alias_name = match &alias_val {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        other => {
            return Err(Error::type_error_in("alias", "symbol", other.type_name()));
        }
    };

    // Get target namespace symbol
    let ns_val = eval(&args[1], env)?;
    let ns_name = match &ns_val {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "alias",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();

    // Find or create the target namespace
    let target_ns = registry
        .find(&ns_name)
        .ok_or_else(|| Error::namespace_not_found(&ns_name))?;

    // Add alias to current namespace
    let current_ns = registry.current();
    current_ns.add_alias(alias_name, target_ns);

    Ok(KlujurVal::Nil)
}

/// Parse a require spec which can be:
/// - A symbol: 'mylib.utils
/// - A vector: '[mylib.utils :as u :refer [foo bar]]
fn parse_require_spec(spec: &KlujurVal) -> Result<(String, RequireOpts)> {
    match spec {
        KlujurVal::Symbol(s, _) => Ok((s.name().to_string(), RequireOpts::default())),
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                return Err(Error::syntax("require", "spec vector cannot be empty"));
            }

            // First element is the namespace name
            let ns_name = match &items[0] {
                KlujurVal::Symbol(s, _) => s.name().to_string(),
                other => {
                    return Err(Error::type_error_in("require", "symbol", other.type_name()));
                }
            };

            let mut opts = RequireOpts::default();
            let mut i = 1;

            while i < items.len() {
                match &items[i] {
                    KlujurVal::Keyword(kw) if kw.name() == "as" => {
                        if i + 1 >= items.len() {
                            return Err(Error::syntax("require", ":as requires a symbol"));
                        }
                        if let KlujurVal::Symbol(s, _) = &items[i + 1] {
                            opts.alias = Some(s.name().to_string());
                        } else {
                            return Err(Error::syntax("require", ":as requires a symbol"));
                        }
                        i += 2;
                    }
                    KlujurVal::Keyword(kw) if kw.name() == "refer" => {
                        if i + 1 >= items.len() {
                            return Err(Error::syntax(
                                "require",
                                ":refer requires a vector or :all",
                            ));
                        }
                        match &items[i + 1] {
                            KlujurVal::Vector(refs, _) => {
                                let names: Vec<String> = refs
                                    .iter()
                                    .filter_map(|v| match v {
                                        KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                        _ => None,
                                    })
                                    .collect();
                                opts.refer = Some(ReferSpec::Only(names));
                            }
                            KlujurVal::Keyword(kw) if kw.name() == "all" => {
                                opts.refer = Some(ReferSpec::All);
                            }
                            _ => {
                                return Err(Error::syntax(
                                    "require",
                                    ":refer requires a vector or :all",
                                ));
                            }
                        }
                        i += 2;
                    }
                    _ => {
                        i += 1;
                    }
                }
            }

            Ok((ns_name, opts))
        }
        other => Err(Error::type_error_in(
            "require",
            "symbol or vector",
            other.type_name(),
        )),
    }
}

#[derive(Default)]
struct RequireOpts {
    alias: Option<String>,
    refer: Option<ReferSpec>,
}

enum ReferSpec {
    All,
    Only(Vec<String>),
}

/// (require spec...) - Load and require namespaces
///
/// Supported forms:
/// - (require 'mylib.utils)
/// - (require '[mylib.utils :as u])
/// - (require '[mylib.utils :refer [foo bar]])
/// - (require '[mylib.utils :refer :all])
/// - (require 'ns1 'ns2 '[ns3 :as n])
///
/// Flags (can appear anywhere):
/// - :reload - reload namespace even if already loaded
/// - :reload-all - reload namespace and all its dependencies
pub(crate) fn eval_require(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("require", "requires at least 1 argument"));
    }

    let registry = env.registry();
    let mut reload = false;
    let mut reload_all = false;

    // First pass: check for :reload or :reload-all flags
    for arg in args {
        let val = eval(arg, env)?;
        if let KlujurVal::Keyword(kw) = &val {
            match kw.name() {
                "reload" => reload = true,
                "reload-all" => reload_all = true,
                _ => {}
            }
        }
    }

    // Save the original namespace before processing (files may switch namespaces)
    let original_ns_name = registry.current_name();

    // Process each require spec
    for arg in args {
        let val = eval(arg, env)?;

        // Skip flags
        if let KlujurVal::Keyword(kw) = &val
            && (kw.name() == "reload" || kw.name() == "reload-all")
        {
            continue;
        }

        let (ns_name, opts) = parse_require_spec(&val)?;

        // Check if we need to load
        let should_load = reload || reload_all || !registry.is_loaded(&ns_name);

        if should_load {
            // Mark for reload if requested
            if reload || reload_all {
                registry.reload(&ns_name);
            }

            // Find the file
            if let Some(path) = registry.find_namespace_file(&ns_name) {
                // Load the file
                let content = std::fs::read_to_string(&path)
                    .map_err(|e| Error::io("Reading file", Some(path.display().to_string()), e))?;

                let mut parser = klujur_parser::Parser::new(&content)
                    .map_err(|e| Error::parse_error(format!("{:?}", e)))?;

                while let Some(form) = parser
                    .parse()
                    .map_err(|e| Error::parse_error(format!("{:?}", e)))?
                {
                    eval(&form, env)?;
                }

                registry.mark_loaded(&ns_name);

                // Restore original namespace after loading
                registry.set_current(&original_ns_name);
            } else if registry.find(&ns_name).is_none() {
                // Namespace doesn't exist and no file found
                return Err(Error::namespace_not_found(format!(
                    "{} (searched load paths: {:?})",
                    ns_name,
                    registry.load_paths()
                )));
            }
            // If namespace exists but no file, that's OK (might be builtin)
        }

        // Get the original namespace (use find_or_create in case it was just created)
        let current_ns = registry.find_or_create(&original_ns_name);

        // Apply :as alias
        if let Some(alias) = opts.alias
            && let Some(target_ns) = registry.find(&ns_name)
        {
            current_ns.add_alias(alias, target_ns);
        }

        // Apply :refer
        if let Some(refer_spec) = opts.refer
            && let Some(source_ns) = registry.find(&ns_name)
        {
            let publics = source_ns.publics();
            match refer_spec {
                ReferSpec::All => {
                    for (name, var) in publics {
                        current_ns.refer(name, var);
                    }
                }
                ReferSpec::Only(names) => {
                    for name in names {
                        if let Some(var) = publics.get(&name) {
                            current_ns.refer(name, var.clone());
                        } else if source_ns.interns().contains_key(&name) {
                            return Err(Error::not_public(&name, &ns_name));
                        } else {
                            return Err(Error::UndefinedSymbol(Symbol::with_namespace(
                                &ns_name, &name,
                            )));
                        }
                    }
                }
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// (use spec...) - Load namespace and refer all public vars (deprecated)
///
/// Equivalent to (require '[ns :refer :all]).
/// Supports :only, :exclude, :rename filters like refer.
pub(crate) fn eval_use(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("use", "requires at least 1 argument"));
    }

    let registry = env.registry();
    // Save the original namespace before processing (files may switch namespaces)
    let original_ns_name = registry.current_name();

    for arg in args {
        let val = eval(arg, env)?;

        // Parse namespace and options
        let (ns_name, only, exclude, rename) = match &val {
            KlujurVal::Symbol(s, _) => (
                s.name().to_string(),
                None,
                vec![],
                std::collections::HashMap::new(),
            ),
            KlujurVal::Vector(items, _) if !items.is_empty() => {
                let ns_name = match &items[0] {
                    KlujurVal::Symbol(s, _) => s.name().to_string(),
                    other => return Err(Error::type_error_in("use", "symbol", other.type_name())),
                };

                let mut only: Option<Vec<String>> = None;
                let mut exclude: Vec<String> = vec![];
                let mut rename: std::collections::HashMap<String, String> =
                    std::collections::HashMap::new();

                let mut i = 1;
                while i < items.len() {
                    match &items[i] {
                        KlujurVal::Keyword(kw) if kw.name() == "only" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Vector(refs, _) = &items[i + 1]
                            {
                                only = Some(
                                    refs.iter()
                                        .filter_map(|v| match v {
                                            KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                            _ => None,
                                        })
                                        .collect(),
                                );
                            }
                            i += 2;
                        }
                        KlujurVal::Keyword(kw) if kw.name() == "exclude" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Vector(refs, _) = &items[i + 1]
                            {
                                exclude = refs
                                    .iter()
                                    .filter_map(|v| match v {
                                        KlujurVal::Symbol(s, _) => Some(s.name().to_string()),
                                        _ => None,
                                    })
                                    .collect();
                            }
                            i += 2;
                        }
                        KlujurVal::Keyword(kw) if kw.name() == "rename" => {
                            if i + 1 < items.len()
                                && let KlujurVal::Map(map, _) = &items[i + 1]
                            {
                                for (k, v) in map.iter() {
                                    if let (KlujurVal::Symbol(ks, _), KlujurVal::Symbol(vs, _)) =
                                        (k, v)
                                    {
                                        rename.insert(ks.name().to_string(), vs.name().to_string());
                                    }
                                }
                            }
                            i += 2;
                        }
                        _ => i += 1,
                    }
                }

                (ns_name, only, exclude, rename)
            }
            other => {
                return Err(Error::type_error_in(
                    "use",
                    "symbol or vector",
                    other.type_name(),
                ));
            }
        };

        // Load namespace if not loaded
        if !registry.is_loaded(&ns_name) {
            if let Some(path) = registry.find_namespace_file(&ns_name) {
                let content = std::fs::read_to_string(&path)
                    .map_err(|e| Error::io("Reading file", Some(path.display().to_string()), e))?;

                let mut parser = klujur_parser::Parser::new(&content)
                    .map_err(|e| Error::parse_error(format!("{:?}", e)))?;

                while let Some(form) = parser
                    .parse()
                    .map_err(|e| Error::parse_error(format!("{:?}", e)))?
                {
                    eval(&form, env)?;
                }

                registry.mark_loaded(&ns_name);

                // Restore original namespace after loading (file may have switched namespaces)
                registry.set_current(&original_ns_name);
            } else if registry.find(&ns_name).is_none() {
                return Err(Error::namespace_not_found(&ns_name));
            }
        }

        // Refer vars from namespace (use original namespace, not whatever the loaded file switched to)
        if let Some(source_ns) = registry.find(&ns_name) {
            let current_ns = registry.find_or_create(&original_ns_name);
            let publics = source_ns.publics();

            let vars_to_refer: Vec<(String, _)> = match only {
                Some(only_list) => only_list
                    .into_iter()
                    .filter(|name| !exclude.contains(name))
                    .filter_map(|name| {
                        publics.get(&name).map(|var| {
                            let refer_name = rename.get(&name).cloned().unwrap_or(name);
                            (refer_name, var.clone())
                        })
                    })
                    .collect(),
                None => publics
                    .into_iter()
                    .filter(|(name, _)| !exclude.contains(name))
                    .map(|(name, var)| {
                        let refer_name = rename.get(&name).cloned().unwrap_or(name);
                        (refer_name, var)
                    })
                    .collect(),
            };

            for (name, var) in vars_to_refer {
                current_ns.refer(name, var);
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// (all-ns) - Returns a sequence of all namespaces
pub(crate) fn eval_all_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::syntax("all-ns", "takes no arguments"));
    }

    let registry = env.registry();
    let ns_names = registry.all_ns();

    let ns_symbols: Vec<KlujurVal> = ns_names
        .into_iter()
        .map(|name| KlujurVal::symbol(Symbol::new(&name)))
        .collect();

    Ok(KlujurVal::list(ns_symbols))
}

/// (find-ns sym) - Returns the namespace named by the symbol, or nil if not found
pub(crate) fn eval_find_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("find-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "find-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    match registry.find(&ns_name) {
        Some(_) => Ok(KlujurVal::symbol(Symbol::new(&ns_name))),
        None => Ok(KlujurVal::Nil),
    }
}

/// (create-ns sym) - Creates a namespace with the given name if it doesn't exist, returns it
pub(crate) fn eval_create_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("create-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "create-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    registry.find_or_create(&ns_name);

    Ok(KlujurVal::symbol(Symbol::new(&ns_name)))
}

/// (remove-ns sym) - Removes the namespace from the registry, returns nil
pub(crate) fn eval_remove_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("remove-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "remove-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    if !registry.remove_ns(&ns_name) {
        // Could not remove - either doesn't exist or is current namespace
        if registry.current_name() == ns_name {
            return Err(Error::EvalError(
                "Cannot remove current namespace".to_string(),
            ));
        }
    }

    Ok(KlujurVal::Nil)
}

/// (the-ns sym) - Returns the namespace named by the symbol, throws if not found
pub(crate) fn eval_the_ns(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("the-ns", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "the-ns",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    let registry = env.registry();
    match registry.find(&ns_name) {
        Some(_) => Ok(KlujurVal::symbol(Symbol::new(&ns_name))),
        None => Err(Error::EvalError(format!("No namespace: {}", ns_name))),
    }
}

/// (ns-name ns) - Returns the name of the namespace as a symbol
pub(crate) fn eval_ns_name(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("ns-name", "requires exactly 1 argument"));
    }

    let arg = eval(&args[0], env)?;
    let ns_name = match &arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "ns-name",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    // Verify namespace exists
    let registry = env.registry();
    registry
        .find(&ns_name)
        .ok_or_else(|| Error::namespace_not_found(&ns_name))?;

    Ok(KlujurVal::symbol(Symbol::new(&ns_name)))
}

/// (ns-resolve ns sym) or (ns-resolve ns env sym)
/// Returns the var to which a symbol will be resolved in the namespace, else nil.
/// If the symbol is qualified, the namespace argument is ignored.
/// The 3-arity form accepts an environment map (for macro &env) - if the symbol
/// is found in the env, returns nil (it's a local binding, not a var).
pub(crate) fn eval_ns_resolve(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    // Parse arguments based on arity
    let (ns_arg, env_map, sym) = match args.len() {
        2 => {
            // (ns-resolve ns sym)
            let ns_arg = eval(&args[0], env)?;
            let sym = eval(&args[1], env)?;
            (ns_arg, None, sym)
        }
        3 => {
            // (ns-resolve ns env sym)
            let ns_arg = eval(&args[0], env)?;
            let env_map = eval(&args[1], env)?;
            let sym = eval(&args[2], env)?;
            (ns_arg, Some(env_map), sym)
        }
        _ => {
            return Err(Error::syntax(
                "ns-resolve",
                "requires 2 or 3 arguments: (ns-resolve ns sym) or (ns-resolve ns env sym)",
            ));
        }
    };

    // sym must be a symbol
    let sym = match &sym {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::type_error_in(
                "ns-resolve",
                "symbol",
                other.type_name(),
            ));
        }
    };

    // If env map is provided, check if symbol is a local binding
    if let Some(KlujurVal::Map(map, _)) = &env_map {
        let sym_val = KlujurVal::symbol(sym.clone());
        if map.contains_key(&sym_val) {
            // Symbol is a local binding, not a var
            return Ok(KlujurVal::Nil);
        }
    }

    let registry = env.registry();

    // If symbol is qualified, resolve using its namespace (ignore ns argument)
    if let Some(sym_ns) = sym.namespace() {
        if let Some(target_ns) = registry.find(sym_ns)
            && let Some(var) = target_ns.find_var(sym.name())
        {
            return Ok(KlujurVal::Var(var));
        }
        return Ok(KlujurVal::Nil);
    }

    // Get the namespace from argument
    let ns_name = match &ns_arg {
        KlujurVal::Symbol(s, _) => s.name().to_string(),
        KlujurVal::String(s) => s.to_string(),
        other => {
            return Err(Error::type_error_in(
                "ns-resolve",
                "symbol or string",
                other.type_name(),
            ));
        }
    };

    // Find the namespace
    let target_ns = match registry.find(&ns_name) {
        Some(ns) => ns,
        None => return Ok(KlujurVal::Nil),
    };

    // Resolve the symbol in that namespace (checks local vars, then refers)
    match target_ns.resolve(&sym) {
        Some(var) => Ok(KlujurVal::Var(var)),
        None => Ok(KlujurVal::Nil),
    }
}

/// (resolve sym) - resolve a symbol to a var in the current namespace
/// Returns the var if found, nil otherwise.
/// This is a simpler version of ns-resolve that uses the current namespace.
pub(crate) fn eval_resolve(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::syntax("resolve", "requires exactly 1 argument"));
    }

    let sym_val = eval(&args[0], env)?;
    let sym = match sym_val {
        KlujurVal::Symbol(s, _) => s,
        other => {
            return Err(Error::type_error_in("resolve", "symbol", other.type_name()));
        }
    };

    let registry = env.registry();

    // If symbol is qualified, look up directly in its namespace
    if let Some(ns_name) = sym.namespace() {
        match registry.find(ns_name) {
            Some(ns) => match ns.resolve(&sym) {
                Some(var) => Ok(KlujurVal::Var(var)),
                None => Ok(KlujurVal::Nil),
            },
            None => Ok(KlujurVal::Nil),
        }
    } else {
        // Unqualified symbol - resolve in current namespace
        let current_ns = registry.current();
        match current_ns.resolve(&sym) {
            Some(var) => Ok(KlujurVal::Var(var)),
            None => Ok(KlujurVal::Nil),
        }
    }
}
