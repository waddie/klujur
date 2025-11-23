// klujur-core - Protocol special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Protocol special forms: defprotocol, extend-type

use std::rc::Rc;

use klujur_parser::{KlujurVal, MethodSignature, Protocol, Symbol, TypeKey};

use crate::env::Env;
use crate::error::{Error, Result};

use super::{apply, eval, make_native_fn};

// ============================================================================
// Protocol Special Forms
// ============================================================================

/// (defprotocol Name
///   "Optional docstring"
///   (method-name [this arg1 arg2] "Method docstring")
///   (other-method [this] [this x] "Multiple arities"))
pub(crate) fn eval_defprotocol(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("defprotocol", "requires a name"));
    }

    // Get the protocol name
    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defprotocol",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    let registry = env.registry();
    let ns_name = registry.current_name();

    // Create the protocol
    let mut protocol = Protocol::new(name.clone(), ns_name.clone());

    let mut i = 1;

    // Skip docstring if present
    if args
        .get(i)
        .map(|v| matches!(v, KlujurVal::String(_)))
        .unwrap_or(false)
    {
        i += 1;
    }

    // Parse method signatures
    while i < args.len() {
        let method_form = match &args[i] {
            KlujurVal::List(items, _) => items.iter().cloned().collect::<Vec<_>>(),
            other => {
                return Err(Error::syntax(
                    "defprotocol",
                    format!("method signature must be a list, got {}", other.type_name()),
                ));
            }
        };

        if method_form.is_empty() {
            return Err(Error::syntax(
                "defprotocol",
                "method signature cannot be empty",
            ));
        }

        let method_name = match &method_form[0] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "defprotocol",
                    format!("method name must be a symbol, got {}", other.type_name()),
                ));
            }
        };

        let mut arglists = Vec::new();
        let mut doc = None;

        for item in method_form.iter().skip(1) {
            match item {
                KlujurVal::Vector(params, _) => {
                    // Parse arglist
                    let mut arg_symbols = Vec::new();
                    for param in params.iter() {
                        if let KlujurVal::Symbol(s, _) = param {
                            arg_symbols.push(s.clone());
                        }
                    }
                    arglists.push(arg_symbols);
                }
                KlujurVal::String(s) => {
                    doc = Some(s.to_string());
                }
                _ => {}
            }
        }

        if arglists.is_empty() {
            return Err(Error::syntax(
                "defprotocol",
                format!("method {} requires at least one arglist", method_name),
            ));
        }

        protocol.add_method(MethodSignature {
            name: method_name.clone(),
            arglists,
            doc,
        });

        i += 1;
    }

    // Register the protocol
    let proto_rc = registry.register_protocol(protocol);

    // Create dispatch functions for each method and intern them as vars
    let current_ns = registry.current();
    for method_name_str in proto_rc.methods.keys() {
        let dispatch_fn = create_protocol_dispatch_fn(proto_rc.clone(), method_name_str.clone());
        current_ns.intern_with_value(method_name_str.clone(), dispatch_fn);
    }

    // Also intern the protocol itself as a var
    let proto_val = KlujurVal::from_protocol(proto_rc);
    current_ns.intern_with_value(name.name().to_string(), proto_val.clone());

    Ok(proto_val)
}

/// Create a protocol dispatch function.
/// This returns a NativeFn that dispatches based on the first argument's type.
fn create_protocol_dispatch_fn(protocol: Rc<Protocol>, method_name: String) -> KlujurVal {
    let proto = protocol.clone();
    let name = method_name.clone();

    // Create a closure that performs protocol dispatch
    let dispatch_fn = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.is_empty() {
            return Err(Error::EvalError(format!(
                "Protocol method {} requires at least one argument",
                name
            )));
        }

        let first_arg = &args[0];
        let type_key = first_arg.type_key();

        // Look up the implementation for this type
        let impls = proto.impls.borrow();
        let type_impl = impls.get(&type_key).ok_or_else(|| {
            Error::EvalError(format!(
                "No implementation of method {} for type {:?}",
                name, type_key
            ))
        })?;

        let method_fn = type_impl.methods.get(&name).ok_or_else(|| {
            Error::EvalError(format!(
                "Method {} not implemented for type {:?}",
                name, type_key
            ))
        })?;

        // Apply the method function with the args
        apply(method_fn, args)
    };

    KlujurVal::NativeFn(make_native_fn(
        Box::leak(method_name.into_boxed_str()),
        dispatch_fn,
    ))
}

/// (extend-type TypeName
///   ProtocolName
///   (method-name [this arg] body)
///   ...)
pub(crate) fn eval_extend_type(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("extend-type", "requires a type name"));
    }

    // Get the type name - handle both symbol and nil literal
    let type_key = match &args[0] {
        KlujurVal::Symbol(s, _) => symbol_to_type_key(s)?,
        KlujurVal::Nil => TypeKey::Nil, // Support (extend-type nil ...)
        other => {
            return Err(Error::syntax(
                "extend-type",
                format!(
                    "first argument must be a type symbol, got {}",
                    other.type_name()
                ),
            ));
        }
    };
    let registry = env.registry();

    let mut i = 1;
    while i < args.len() {
        // Get protocol name
        let protocol_name = match &args[i] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "extend-type",
                    format!("expected protocol name, got {}", other.type_name()),
                ));
            }
        };

        // Find the protocol
        let protocol = registry
            .resolve_protocol(protocol_name.name())
            .ok_or_else(|| Error::EvalError(format!("Unknown protocol: {}", protocol_name)))?;

        i += 1;

        // Collect method implementations until next protocol name or end
        while i < args.len() {
            // Check if this is a method implementation (list starting with symbol)
            match &args[i] {
                KlujurVal::List(items, _) if !items.is_empty() => {
                    if let KlujurVal::Symbol(method_sym, _) = &items[0] {
                        let method_name = method_sym.name().to_string();

                        // Check if this method exists in the protocol
                        if !protocol.methods.contains_key(&method_name) {
                            return Err(Error::EvalError(format!(
                                "Method {} is not part of protocol {}",
                                method_name, protocol_name
                            )));
                        }

                        // Build a function from (method-name [args] body)
                        // Convert to (fn [args] body)
                        let fn_args: Vec<KlujurVal> = items.iter().skip(1).cloned().collect();
                        let fn_form = KlujurVal::list(
                            std::iter::once(KlujurVal::Symbol(Symbol::new("fn"), None))
                                .chain(fn_args)
                                .collect(),
                        );

                        // Evaluate the fn form to create the function
                        let method_fn = eval(&fn_form, env)?;

                        // Add the method implementation to the protocol
                        protocol.add_method_impl(type_key.clone(), method_name, method_fn);

                        i += 1;
                    } else {
                        // Not a method impl, must be next protocol
                        break;
                    }
                }
                KlujurVal::Symbol(_, _) => {
                    // This is the next protocol name
                    break;
                }
                other => {
                    return Err(Error::syntax(
                        "extend-type",
                        format!(
                            "expected method implementation or protocol name, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }
        }
    }

    Ok(KlujurVal::Nil)
}

/// (extend TypeName
///   Protocol {:method-name fn, ...}
///   Protocol2 {:method-name fn, ...})
///
/// Low-level protocol extension that takes a map of keyword->fn pairs.
pub(crate) fn eval_extend(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("extend", "requires a type name"));
    }

    // Get the type name - handle both symbol and nil literal
    let type_key = match &args[0] {
        KlujurVal::Symbol(s, _) => symbol_to_type_key(s)?,
        KlujurVal::Nil => TypeKey::Nil, // Support (extend nil ...)
        other => {
            return Err(Error::syntax(
                "extend",
                format!(
                    "first argument must be a type symbol, got {}",
                    other.type_name()
                ),
            ));
        }
    };
    let registry = env.registry();

    // Process pairs of (Protocol method-map)
    let mut i = 1;
    while i < args.len() {
        // Get protocol - can be a symbol or the protocol value itself
        let protocol = match &args[i] {
            KlujurVal::Symbol(s, _) => registry
                .resolve_protocol(s.name())
                .ok_or_else(|| Error::EvalError(format!("Unknown protocol: {}", s)))?,
            KlujurVal::Protocol(p) => p.0.clone(),
            other => {
                return Err(Error::syntax(
                    "extend",
                    format!("expected protocol name or value, got {}", other.type_name()),
                ));
            }
        };

        i += 1;

        if i >= args.len() {
            return Err(Error::syntax(
                "extend",
                "protocol must be followed by a method map",
            ));
        }

        // Get method map - must be a map
        let method_map = eval(&args[i], env)?;
        let methods = match &method_map {
            KlujurVal::Map(m, _) => m,
            other => {
                return Err(Error::syntax(
                    "extend",
                    format!("expected method map, got {}", other.type_name()),
                ));
            }
        };

        // Process each method in the map
        for (key, val) in methods.iter() {
            let method_name = match key {
                KlujurVal::Keyword(k) => k.name().to_string(),
                KlujurVal::Symbol(s, _) => s.name().to_string(),
                KlujurVal::String(s) => s.to_string(),
                other => {
                    return Err(Error::syntax(
                        "extend",
                        format!(
                            "method key must be keyword, symbol, or string, got {}",
                            other.type_name()
                        ),
                    ));
                }
            };

            // Validate method exists in protocol
            if !protocol.methods.contains_key(&method_name) {
                return Err(Error::EvalError(format!(
                    "Method {} is not part of protocol {}",
                    method_name, protocol.name
                )));
            }

            // Validate value is a function
            match val {
                KlujurVal::Fn(_) | KlujurVal::NativeFn(_) | KlujurVal::Macro(_) => {}
                other => {
                    return Err(Error::syntax(
                        "extend",
                        format!(
                            "method implementation must be a function, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }

            // Add the method implementation
            protocol.add_method_impl(type_key.clone(), method_name, val.clone());
        }

        i += 1;
    }

    Ok(KlujurVal::Nil)
}

/// Convert a type name symbol to a TypeKey
pub(crate) fn symbol_to_type_key(sym: &Symbol) -> Result<TypeKey> {
    match sym.name() {
        "nil" => Ok(TypeKey::Nil),
        "Boolean" | "Bool" => Ok(TypeKey::Bool),
        "Integer" | "Long" | "Int" => Ok(TypeKey::Int),
        "Float" | "Double" => Ok(TypeKey::Float),
        "Ratio" => Ok(TypeKey::Ratio),
        "Char" | "Character" => Ok(TypeKey::Char),
        "String" => Ok(TypeKey::String),
        "Symbol" => Ok(TypeKey::Symbol),
        "Keyword" => Ok(TypeKey::Keyword),
        "List" | "PersistentList" => Ok(TypeKey::List),
        "Vector" | "PersistentVector" => Ok(TypeKey::Vector),
        "Map" | "HashMap" | "PersistentHashMap" => Ok(TypeKey::Map),
        "Set" | "HashSet" | "PersistentHashSet" => Ok(TypeKey::Set),
        "Fn" | "Function" | "IFn" => Ok(TypeKey::Fn),
        "Var" => Ok(TypeKey::Var),
        "Atom" => Ok(TypeKey::Atom),
        "Delay" => Ok(TypeKey::Delay),
        "LazySeq" => Ok(TypeKey::LazySeq),
        "Multimethod" => Ok(TypeKey::Multimethod),
        "Hierarchy" => Ok(TypeKey::Hierarchy),
        "Reduced" => Ok(TypeKey::Reduced),
        "Volatile" => Ok(TypeKey::Volatile),
        name => Ok(TypeKey::Record(Symbol::new(name))),
    }
}
