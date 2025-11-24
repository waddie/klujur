// klujur-core - Record special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Record special forms: defrecord

use std::any::Any;
use std::collections::HashMap;
use std::rc::Rc;

use klujur_parser::{
    FnArity, Keyword, KlujurFn, KlujurVal, RecordDef, RecordInstance, Symbol, TypeKey,
};

use crate::env::Env;
use crate::error::{Error, Result};

use super::make_native_fn;

// ============================================================================
// Record Special Forms
// ============================================================================

/// (defrecord RecordName [field1 field2 ...]
///   ProtocolName
///   (method-name [this arg] body)
///   ...)
pub(crate) fn eval_defrecord(args: &[KlujurVal], env: &Env) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::syntax("defrecord", "requires a name"));
    }

    // Get the record name
    let name = match &args[0] {
        KlujurVal::Symbol(s, _) => s.clone(),
        other => {
            return Err(Error::syntax(
                "defrecord",
                format!("first argument must be a symbol, got {}", other.type_name()),
            ));
        }
    };

    if args.len() < 2 {
        return Err(Error::syntax("defrecord", "requires a field vector"));
    }

    // Get the field vector
    let fields: Vec<Symbol> = match &args[1] {
        KlujurVal::Vector(items, _) => {
            let mut fields = Vec::new();
            for item in items.iter() {
                match item {
                    KlujurVal::Symbol(s, _) => fields.push(s.clone()),
                    other => {
                        return Err(Error::syntax(
                            "defrecord",
                            format!("field must be a symbol, got {}", other.type_name()),
                        ));
                    }
                }
            }
            fields
        }
        other => {
            return Err(Error::syntax(
                "defrecord",
                format!(
                    "second argument must be a vector, got {}",
                    other.type_name()
                ),
            ));
        }
    };

    let registry = env.registry();
    let current_ns_name = registry.current_name();

    // Create and register the record definition
    let record_def = RecordDef::new(name.clone(), current_ns_name.clone(), fields.clone());
    registry.register_record(record_def);

    // Create positional constructor: ->RecordName
    let positional_ctor =
        create_positional_record_constructor(name.clone(), current_ns_name.clone(), fields.clone());
    let ctor_name = format!("->{}", name.name());
    let current_ns = registry.current();
    current_ns.intern_with_value(&ctor_name, positional_ctor);

    // Create map constructor: map->RecordName
    let map_ctor =
        create_map_record_constructor(name.clone(), current_ns_name.clone(), fields.clone());
    let map_ctor_name = format!("map->{}", name.name());
    current_ns.intern_with_value(&map_ctor_name, map_ctor);

    // Parse inline protocol implementations (args[2..])
    let mut i = 2;
    while i < args.len() {
        // Expect a protocol name
        let protocol_name = match &args[i] {
            KlujurVal::Symbol(s, _) => s.clone(),
            other => {
                return Err(Error::syntax(
                    "defrecord",
                    format!("expected protocol name symbol, got {}", other.type_name()),
                ));
            }
        };
        i += 1;

        // Look up the protocol
        let protocol = registry
            .resolve_protocol(protocol_name.name())
            .ok_or_else(|| Error::protocol_not_found(protocol_name.name()))?;

        // Collect method implementations until we hit another symbol or end
        while i < args.len() {
            match &args[i] {
                KlujurVal::List(items, _) => {
                    let method_form: Vec<_> = items.iter().cloned().collect();
                    if method_form.is_empty() {
                        return Err(Error::syntax(
                            "defrecord",
                            "method implementation cannot be empty",
                        ));
                    }

                    // Parse method: (method-name [args] body...)
                    let method_name = match &method_form[0] {
                        KlujurVal::Symbol(s, _) => s.name().to_string(),
                        other => {
                            return Err(Error::syntax(
                                "defrecord",
                                format!("method name must be a symbol, got {}", other.type_name()),
                            ));
                        }
                    };

                    // Parse args vector and body
                    if method_form.len() < 2 {
                        return Err(Error::syntax(
                            "defrecord",
                            format!("method {} requires args and body", method_name),
                        ));
                    }

                    let params_vec = match &method_form[1] {
                        KlujurVal::Vector(v, _) => v.iter().cloned().collect::<Vec<_>>(),
                        other => {
                            return Err(Error::syntax(
                                "defrecord",
                                format!(
                                    "method {} args must be a vector, got {}",
                                    method_name,
                                    other.type_name()
                                ),
                            ));
                        }
                    };

                    let body = method_form[2..].to_vec();

                    // Parse param symbols
                    let params: Vec<Symbol> = params_vec
                        .iter()
                        .map(|p| match p {
                            KlujurVal::Symbol(s, _) => Ok(s.clone()),
                            other => Err(Error::syntax(
                                "defrecord",
                                format!("param must be symbol, got {}", other.type_name()),
                            )),
                        })
                        .collect::<Result<Vec<_>>>()?;

                    // Create the method function
                    let method_fn = create_fn_from_parts(params, body, env.clone());

                    // Register the implementation
                    let type_key = TypeKey::Record(name.clone());
                    protocol.add_method_impl(type_key, method_name, method_fn);

                    i += 1;
                }
                KlujurVal::Symbol(_, _) => {
                    // This is the next protocol name
                    break;
                }
                other => {
                    return Err(Error::syntax(
                        "defrecord",
                        format!(
                            "expected method implementation or protocol name, got {}",
                            other.type_name()
                        ),
                    ));
                }
            }
        }
    }

    // Return the record name symbol
    Ok(KlujurVal::Symbol(name, None))
}

/// Create a positional constructor function: ->RecordName
fn create_positional_record_constructor(
    record_type: Symbol,
    record_ns: String,
    fields: Vec<Symbol>,
) -> KlujurVal {
    let arity = fields.len();
    let name = format!("->{}", record_type.name());

    let constructor = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.len() != arity {
            return Err(Error::arity(arity, args.len()));
        }

        let mut values = HashMap::new();
        for (field, value) in fields.iter().zip(args.iter()) {
            let key = Keyword::new(field.name());
            values.insert(key, value.clone());
        }

        Ok(KlujurVal::record(RecordInstance::new(
            record_type.clone(),
            record_ns.clone(),
            fields.clone(),
            values,
        )))
    };

    KlujurVal::NativeFn(make_native_fn(name, constructor))
}

/// Create a map constructor function: map->RecordName
fn create_map_record_constructor(
    record_type: Symbol,
    record_ns: String,
    fields: Vec<Symbol>,
) -> KlujurVal {
    let name = format!("map->{}", record_type.name());

    let constructor = move |args: &[KlujurVal]| -> Result<KlujurVal> {
        if args.len() != 1 {
            return Err(Error::arity(1, args.len()));
        }

        let map = match &args[0] {
            KlujurVal::Map(m, _) => m,
            other => {
                return Err(Error::type_error("map", other.type_name()));
            }
        };

        let mut values = HashMap::new();

        // Extract required fields
        for field in &fields {
            let key = KlujurVal::Keyword(Keyword::new(field.name()));
            let value = map
                .get(&key)
                .ok_or_else(|| Error::missing_field(record_type.name(), field.name()))?;
            values.insert(Keyword::new(field.name()), value.clone());
        }

        // Include any extra keys from the map
        for (k, v) in map.iter() {
            if let KlujurVal::Keyword(kw) = k
                && !values.contains_key(kw)
            {
                values.insert(kw.clone(), v.clone());
            }
        }

        Ok(KlujurVal::record(RecordInstance::new(
            record_type.clone(),
            record_ns.clone(),
            fields.clone(),
            values,
        )))
    };

    KlujurVal::NativeFn(make_native_fn(name, constructor))
}

/// Helper to create a function from params and body
fn create_fn_from_parts(params: Vec<Symbol>, body: Vec<KlujurVal>, env: Env) -> KlujurVal {
    let arity = FnArity::new(params, None, body);
    let env_any: Rc<dyn Any> = Rc::new(env);
    KlujurVal::Fn(KlujurFn::new_multi(None, vec![arity], env_any))
}
