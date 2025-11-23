// klujur-core - Type predicate built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Type predicates: nil?, some?, boolean?, number?, etc.

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Type Predicates
// ============================================================================

pub(crate) fn builtin_nil_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nil?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Nil)))
}

pub(crate) fn builtin_some_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("some?", 1, args.len()));
    }
    Ok(KlujurVal::bool(!matches!(args[0], KlujurVal::Nil)))
}

pub(crate) fn builtin_boolean_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("boolean?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(_))))
}

pub(crate) fn builtin_number_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("number?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Int(_) | KlujurVal::Float(_) | KlujurVal::Ratio(_, _)
    )))
}

pub(crate) fn builtin_integer_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("integer?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Int(_))))
}

pub(crate) fn builtin_float_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("float?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Float(_))))
}

pub(crate) fn builtin_string_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("string?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::String(_))))
}

pub(crate) fn builtin_symbol_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("symbol?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Symbol(_, _))))
}

pub(crate) fn builtin_keyword_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("keyword?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Keyword(_))))
}

pub(crate) fn builtin_list_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("list?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::List(_, None))))
}

pub(crate) fn builtin_vector_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vector?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, None)
    )))
}

pub(crate) fn builtin_map_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("map?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Map(_, None))))
}

pub(crate) fn builtin_set_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("set?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Set(_, None))))
}

pub(crate) fn builtin_fn_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("fn?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Fn(_) | KlujurVal::NativeFn(_)
    )))
}

pub(crate) fn builtin_coll_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("coll?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
    )))
}

pub(crate) fn builtin_seq_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seq?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::List(_, None))))
}
