// klujur-core - Date/time built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Date/time functions: system-time, now-millis, now-nanos

use std::time::{SystemTime, UNIX_EPOCH};

use klujur_parser::KlujurVal;

use crate::error::{Error, Result};

// ============================================================================
// Time Functions
// ============================================================================

/// (system-time) - returns the current system time as milliseconds since Unix epoch
pub(crate) fn builtin_system_time(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("system-time", 0, args.len()));
    }
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| Error::EvalError(format!("system-time: {}", e)))?;
    Ok(KlujurVal::int(duration.as_millis() as i64))
}

/// (now-millis) - returns the current time in milliseconds since Unix epoch
/// Alias for system-time, matching common Clojure idiom (System/currentTimeMillis)
pub(crate) fn builtin_now_millis(args: &[KlujurVal]) -> Result<KlujurVal> {
    builtin_system_time(args)
}

/// (now-nanos) - returns the current time in nanoseconds since Unix epoch
pub(crate) fn builtin_now_nanos(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("now-nanos", 0, args.len()));
    }
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| Error::EvalError(format!("now-nanos: {}", e)))?;
    Ok(KlujurVal::int(duration.as_nanos() as i64))
}

/// (now-micros) - returns the current time in microseconds since Unix epoch
pub(crate) fn builtin_now_micros(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("now-micros", 0, args.len()));
    }
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| Error::EvalError(format!("now-micros: {}", e)))?;
    Ok(KlujurVal::int(duration.as_micros() as i64))
}

/// (now-secs) - returns the current time in seconds since Unix epoch
pub(crate) fn builtin_now_secs(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("now-secs", 0, args.len()));
    }
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| Error::EvalError(format!("now-secs: {}", e)))?;
    Ok(KlujurVal::int(duration.as_secs() as i64))
}
