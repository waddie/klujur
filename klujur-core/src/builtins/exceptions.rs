// klujur-core - Exception built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Exception operations: ex-info, ex-message, ex-data

use klujur_parser::{Keyword, KlujurVal};

use crate::error::{Error, Result};

// ============================================================================
// Exceptions
// ============================================================================

/// (ex-info msg data) or (ex-info msg data cause) - create an exception info map
/// Returns {:message msg :data data} or {:message msg :data data :cause cause}
pub(crate) fn builtin_ex_info(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::arity_range("ex-info", 2, 3, args.len()));
    }

    let message = match &args[0] {
        KlujurVal::String(s) => KlujurVal::String(s.clone()),
        other => {
            return Err(Error::type_error_in("ex-info", "string", other.type_name()));
        }
    };

    let data = &args[1];
    if !matches!(data, KlujurVal::Map(_, _)) {
        return Err(Error::type_error_in("ex-info", "map", data.type_name()));
    }

    let mut entries = vec![
        (KlujurVal::Keyword(Keyword::new("message")), message),
        (KlujurVal::Keyword(Keyword::new("data")), data.clone()),
    ];

    // Add cause if provided (3-arity)
    if args.len() == 3 {
        entries.push((KlujurVal::Keyword(Keyword::new("cause")), args[2].clone()));
    }

    Ok(KlujurVal::map(entries))
}

/// (ex-message ex) - get the message from an exception
pub(crate) fn builtin_ex_message(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ex-message", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let message_key = KlujurVal::Keyword(Keyword::new("message"));
            Ok(map.get(&message_key).cloned().unwrap_or(KlujurVal::Nil))
        }
        KlujurVal::String(s) => Ok(KlujurVal::String(s.clone())),
        _ => Ok(KlujurVal::Nil),
    }
}

/// (ex-data ex) - get the data map from an exception
pub(crate) fn builtin_ex_data(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ex-data", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let data_key = KlujurVal::Keyword(Keyword::new("data"));
            Ok(map.get(&data_key).cloned().unwrap_or(KlujurVal::Nil))
        }
        _ => Ok(KlujurVal::Nil),
    }
}

/// (ex-cause ex) - get the cause from an exception
pub(crate) fn builtin_ex_cause(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ex-cause", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let cause_key = KlujurVal::Keyword(Keyword::new("cause"));
            Ok(map.get(&cause_key).cloned().unwrap_or(KlujurVal::Nil))
        }
        _ => Ok(KlujurVal::Nil),
    }
}
