// klujur-core - Type checking built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Type operations: type, satisfies?, extends?

use klujur_parser::{KlujurVal, TypeKey};

use crate::error::{Error, Result};

// ============================================================================
// Type Checks
// ============================================================================

/// (type x) - return the type of x
pub(crate) fn builtin_type(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("type", 1, args.len()));
    }
    // For records, return the record type name as a symbol
    if let KlujurVal::Record(r) = &args[0] {
        Ok(KlujurVal::Symbol(r.record_type.clone(), None))
    } else {
        Ok(KlujurVal::string(args[0].type_name()))
    }
}

/// (satisfies? protocol value) - Check if value's type implements the protocol
pub(crate) fn builtin_satisfies_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("satisfies?", 2, args.len()));
    }

    let protocol = match &args[0] {
        KlujurVal::Protocol(p) => p.protocol(),
        other => {
            return Err(Error::type_error("protocol", other.type_name()));
        }
    };

    let value = &args[1];
    let type_key = value.type_key();

    Ok(KlujurVal::Bool(protocol.has_impl(&type_key)))
}

/// (extends? protocol type-symbol) - Check if a type extends the protocol
/// Note: type-symbol should be one of: String, Vector, List, Map, etc.
pub(crate) fn builtin_extends_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("extends?", 2, args.len()));
    }

    let protocol = match &args[0] {
        KlujurVal::Protocol(p) => p.protocol(),
        other => {
            return Err(Error::type_error("protocol", other.type_name()));
        }
    };

    // Convert the type symbol to a TypeKey
    let type_key = match &args[1] {
        KlujurVal::Symbol(sym, _) => match sym.name() {
            "nil" => TypeKey::Nil,
            "Boolean" | "Bool" => TypeKey::Bool,
            "Integer" | "Long" | "Int" => TypeKey::Int,
            "Float" | "Double" => TypeKey::Float,
            "Ratio" => TypeKey::Ratio,
            "Char" | "Character" => TypeKey::Char,
            "String" => TypeKey::String,
            "Symbol" => TypeKey::Symbol,
            "Keyword" => TypeKey::Keyword,
            "List" | "PersistentList" => TypeKey::List,
            "Vector" | "PersistentVector" => TypeKey::Vector,
            "Map" | "HashMap" | "PersistentHashMap" => TypeKey::Map,
            "Set" | "HashSet" | "PersistentHashSet" => TypeKey::Set,
            "Fn" | "Function" | "IFn" => TypeKey::Fn,
            "Var" => TypeKey::Var,
            "Atom" => TypeKey::Atom,
            "Delay" => TypeKey::Delay,
            "LazySeq" => TypeKey::LazySeq,
            "Multimethod" => TypeKey::Multimethod,
            "Hierarchy" => TypeKey::Hierarchy,
            "Reduced" => TypeKey::Reduced,
            "Volatile" => TypeKey::Volatile,
            name => TypeKey::Record(klujur_parser::Symbol::new(name)),
        },
        other => {
            return Err(Error::type_error("symbol", other.type_name()));
        }
    };

    Ok(KlujurVal::Bool(protocol.has_impl(&type_key)))
}
