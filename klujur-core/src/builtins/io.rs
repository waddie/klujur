// klujur-core - I/O built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! I/O operations: print, println, pr-str, read-string, slurp, spit, format
//! Also print-length control functions.

use klujur_parser::{Keyword, KlujurVal, get_print_length, set_print_length};

use crate::error::{Error, Result};

// ============================================================================
// Print Output
// ============================================================================

/// (str & args) - concatenate args as strings
pub(crate) fn builtin_str(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = String::new();
    for arg in args {
        match arg {
            KlujurVal::String(s) => result.push_str(s),
            KlujurVal::Nil => {} // nil contributes nothing
            other => result.push_str(&format!("{}", other)),
        }
    }
    Ok(KlujurVal::string(result))
}

/// (pr-str & args) - print args to string with print representation
pub(crate) fn builtin_pr_str(args: &[KlujurVal]) -> Result<KlujurVal> {
    let parts: Vec<String> = args.iter().map(|a| format!("{}", a)).collect();
    Ok(KlujurVal::string(parts.join(" ")))
}

/// (print & args) - print args without newline
pub(crate) fn builtin_print(args: &[KlujurVal]) -> Result<KlujurVal> {
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        match arg {
            KlujurVal::String(s) => print!("{}", s),
            other => print!("{}", other),
        }
    }
    Ok(KlujurVal::Nil)
}

/// (println & args) - print args with newline
pub(crate) fn builtin_println(args: &[KlujurVal]) -> Result<KlujurVal> {
    builtin_print(args)?;
    println!();
    Ok(KlujurVal::Nil)
}

// ============================================================================
// Print Length Control
// ============================================================================

/// (set-print-length! n) - set the maximum number of elements to print in sequences
/// n can be nil (unlimited) or a positive integer
pub(crate) fn builtin_set_print_length(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("set-print-length!", 1, args.len()));
    }
    let new_len = match &args[0] {
        KlujurVal::Nil => None,
        KlujurVal::Int(n) if *n > 0 => Some(*n as usize),
        KlujurVal::Int(_) => {
            return Err(Error::type_error_in(
                "set-print-length!",
                "positive integer",
                "non-positive integer",
            ));
        }
        other => {
            return Err(Error::type_error_in(
                "set-print-length!",
                "nil or positive integer",
                other.type_name(),
            ));
        }
    };
    let old = set_print_length(new_len);
    Ok(old
        .map(|n| KlujurVal::int(n as i64))
        .unwrap_or(KlujurVal::Nil))
}

/// (get-print-length) - get the current print-length setting
/// Returns nil if unlimited, otherwise the maximum number of elements
pub(crate) fn builtin_get_print_length(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("get-print-length", 0, args.len()));
    }
    Ok(get_print_length()
        .map(|n| KlujurVal::int(n as i64))
        .unwrap_or(KlujurVal::Nil))
}

// ============================================================================
// File I/O
// ============================================================================

/// (read-string s) - parse string to form
pub(crate) fn builtin_read_string(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("read-string", 1, args.len()));
    }
    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => {
            return Err(Error::type_error_in(
                "read-string",
                "string",
                other.type_name(),
            ));
        }
    };

    klujur_parser::Parser::parse_str(s)
        .map_err(|e| Error::EvalError(format!("read-string: {}", e)))?
        .ok_or_else(|| Error::EvalError("read-string: no forms in string".into()))
}

/// (slurp filename) - read file contents as string
pub(crate) fn builtin_slurp(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("slurp", 1, args.len()));
    }
    let path = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("slurp", "string", other.type_name())),
    };

    std::fs::read_to_string(path)
        .map(KlujurVal::string)
        .map_err(|e| Error::io("slurp", Some(path.to_string()), e))
}

/// (spit filename content) or (spit filename content opts) - write to file
pub(crate) fn builtin_spit(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("spit".into()),
        });
    }

    let path = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("spit", "string", other.type_name())),
    };

    let content = match &args[1] {
        KlujurVal::String(s) => s.to_string(),
        other => format!("{}", other),
    };

    let append = if args.len() == 3 {
        // Check for :append true in opts map
        if let KlujurVal::Map(opts, _) = &args[2] {
            opts.get(&KlujurVal::Keyword(Keyword::new("append")))
                .map(|v| v.is_truthy())
                .unwrap_or(false)
        } else {
            false
        }
    } else {
        false
    };

    if append {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(|e| Error::io("spit", Some(path.to_string()), e))?;
        file.write_all(content.as_bytes())
            .map_err(|e| Error::io("spit", Some(path.to_string()), e))?;
    } else {
        std::fs::write(path, content).map_err(|e| Error::io("spit", Some(path.to_string()), e))?;
    }

    Ok(KlujurVal::Nil)
}

// ============================================================================
// String Formatting
// ============================================================================

/// (format fmt & args) - Printf-style string formatting
/// Supports: %s (string), %d (integer), %f (float), %% (literal %)
pub(crate) fn builtin_format(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let fmt_str = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("format", "string", other.type_name())),
    };

    let mut result = String::new();
    let mut arg_idx = 0;
    let format_args = &args[1..];
    let mut chars = fmt_str.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '%' {
            match chars.peek() {
                Some('%') => {
                    result.push('%');
                    chars.next();
                }
                Some('s') => {
                    chars.next();
                    if arg_idx >= format_args.len() {
                        return Err(Error::EvalError(
                            "format: not enough arguments for format string".into(),
                        ));
                    }
                    // %s - convert to string representation
                    match &format_args[arg_idx] {
                        KlujurVal::String(s) => result.push_str(s),
                        KlujurVal::Nil => result.push_str(""),
                        other => result.push_str(&other.to_string()),
                    }
                    arg_idx += 1;
                }
                Some('d') => {
                    chars.next();
                    if arg_idx >= format_args.len() {
                        return Err(Error::EvalError(
                            "format: not enough arguments for format string".into(),
                        ));
                    }
                    // %d - integer
                    match &format_args[arg_idx] {
                        KlujurVal::Int(n) => result.push_str(&n.to_string()),
                        KlujurVal::Float(f) => result.push_str(&(*f as i64).to_string()),
                        other => {
                            return Err(Error::EvalError(format!(
                                "format: %d requires integer, got {}",
                                other.type_name()
                            )));
                        }
                    }
                    arg_idx += 1;
                }
                Some('f') => {
                    chars.next();
                    if arg_idx >= format_args.len() {
                        return Err(Error::EvalError(
                            "format: not enough arguments for format string".into(),
                        ));
                    }
                    // %f - float
                    match &format_args[arg_idx] {
                        KlujurVal::Float(f) => result.push_str(&f.to_string()),
                        KlujurVal::Int(n) => result.push_str(&(*n as f64).to_string()),
                        other => {
                            return Err(Error::EvalError(format!(
                                "format: %f requires number, got {}",
                                other.type_name()
                            )));
                        }
                    }
                    arg_idx += 1;
                }
                Some('n') => {
                    // %n - newline
                    chars.next();
                    result.push('\n');
                }
                Some(ch) => {
                    return Err(Error::EvalError(format!(
                        "format: unknown format specifier %{}",
                        ch
                    )));
                }
                None => {
                    return Err(Error::EvalError(
                        "format: format string ends with lone %".into(),
                    ));
                }
            }
        } else {
            result.push(c);
        }
    }

    Ok(KlujurVal::string(result))
}

// ============================================================================
// System I/O
// ============================================================================

/// (read-line) - reads a line from stdin
/// Returns the line as a string (without trailing newline), or nil on EOF
pub(crate) fn builtin_read_line(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("read-line", 0, args.len()));
    }
    use std::io::BufRead;
    let stdin = std::io::stdin();
    let mut line = String::new();
    match stdin.lock().read_line(&mut line) {
        Ok(0) => Ok(KlujurVal::Nil), // EOF
        Ok(_) => {
            // Remove trailing newline
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            Ok(KlujurVal::string(line))
        }
        Err(e) => Err(Error::io("read-line", None, e)),
    }
}

/// (flush) - flushes stdout
pub(crate) fn builtin_flush(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("flush", 0, args.len()));
    }
    use std::io::Write;
    std::io::stdout()
        .flush()
        .map_err(|e| Error::io("flush", None, e))?;
    Ok(KlujurVal::Nil)
}

// ============================================================================
// Environment Variables
// ============================================================================

/// (getenv name) - get environment variable value
/// Returns the value as a string, or nil if not set
pub(crate) fn builtin_getenv(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("getenv", 1, args.len()));
    }
    let name = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("getenv", "string", other.type_name())),
    };
    match std::env::var(name) {
        Ok(val) => Ok(KlujurVal::string(val)),
        Err(std::env::VarError::NotPresent) => Ok(KlujurVal::Nil),
        Err(std::env::VarError::NotUnicode(_)) => Err(Error::io_msg(
            "getenv",
            Some(name.to_string()),
            "value is not valid UTF-8",
        )),
    }
}

/// (setenv name value) - set environment variable
pub(crate) fn builtin_setenv(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("setenv", 2, args.len()));
    }
    let name = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("setenv", "string", other.type_name())),
    };
    let value = match &args[1] {
        KlujurVal::String(s) => s.to_string(),
        other => format!("{}", other),
    };
    // SAFETY: This function is called from single-threaded Klujur code.
    // We don't modify env vars while iterating over them.
    unsafe { std::env::set_var(name, value) };
    Ok(KlujurVal::Nil)
}

// ============================================================================
// Process Control
// ============================================================================

/// (exit) or (exit code) - exit the process
pub(crate) fn builtin_exit(args: &[KlujurVal]) -> Result<KlujurVal> {
    let code = match args.len() {
        0 => 0,
        1 => match &args[0] {
            KlujurVal::Int(n) => *n as i32,
            other => return Err(Error::type_error_in("exit", "integer", other.type_name())),
        },
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(0, 1),
                got: args.len(),
                name: Some("exit".into()),
            });
        }
    };
    std::process::exit(code);
}
