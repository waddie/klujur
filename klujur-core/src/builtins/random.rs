// klujur-core - Random and utility built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Random operations: rand, rand-int, rand-nth, shuffle
//! Utility operations: gensym, hash

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

use klujur_parser::{KlujurVal, Symbol};

use crate::error::{Error, Result};

use super::{require_int, to_seq};

// ============================================================================
// Random Number Generation
// ============================================================================

// LCG constants (same as used in glibc)
const LCG_MULTIPLIER: u64 = 6364136223846793005;
const LCG_INCREMENT: u64 = 1442695040888963407;

thread_local! {
    /// Persistent RNG state, seeded lazily from system time.
    static RNG_STATE: Cell<u64> = const { Cell::new(0) };
    static RNG_SEEDED: Cell<bool> = const { Cell::new(false) };
}

/// Get the next random u64, advancing the RNG state.
fn next_random_u64() -> u64 {
    RNG_STATE.with(|state| {
        RNG_SEEDED.with(|seeded| {
            if !seeded.get() {
                // Seed lazily from system time
                use std::time::{SystemTime, UNIX_EPOCH};
                let seed = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64;
                state.set(seed);
                seeded.set(true);
            }
        });
        let current = state.get();
        let next = current
            .wrapping_mul(LCG_MULTIPLIER)
            .wrapping_add(LCG_INCREMENT);
        state.set(next);
        next
    })
}

/// Get a random f64 in [0, 1).
fn next_random_f64() -> f64 {
    (next_random_u64() as f64) / (u64::MAX as f64)
}

/// (rand) or (rand n) - random float 0-1 or 0-n
pub(crate) fn builtin_rand(args: &[KlujurVal]) -> Result<KlujurVal> {
    let random = next_random_f64();

    match args.len() {
        0 => Ok(KlujurVal::float(random)),
        1 => match &args[0] {
            KlujurVal::Int(n) => Ok(KlujurVal::float(random * (*n as f64))),
            KlujurVal::Float(n) => Ok(KlujurVal::float(random * n)),
            other => Err(Error::type_error_in("rand", "number", other.type_name())),
        },
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(0, 1),
            got: args.len(),
            name: Some("rand".into()),
        }),
    }
}

/// (rand-int n) - random integer 0 to n-1
pub(crate) fn builtin_rand_int(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rand-int", 1, args.len()));
    }
    let n = require_int("rand-int", &args[0])?;
    if n <= 0 {
        return Err(Error::EvalError("rand-int: n must be positive".into()));
    }

    let random = next_random_u64();
    Ok(KlujurVal::int((random % (n as u64)) as i64))
}

/// (rand-nth coll) - random element from collection
pub(crate) fn builtin_rand_nth(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rand-nth", 1, args.len()));
    }
    let items = to_seq(&args[0])?;
    if items.is_empty() {
        return Err(Error::EvalError("rand-nth: collection is empty".into()));
    }

    let random = next_random_u64();
    let idx = (random % (items.len() as u64)) as usize;
    Ok(items[idx].clone())
}

/// (shuffle coll) - return shuffled collection
pub(crate) fn builtin_shuffle(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("shuffle", 1, args.len()));
    }
    let mut items = to_seq(&args[0])?;

    // Fisher-Yates shuffle
    for i in (1..items.len()).rev() {
        let j = (next_random_u64() % ((i + 1) as u64)) as usize;
        items.swap(i, j);
    }

    Ok(KlujurVal::vector(items))
}

// ============================================================================
// Symbol Generation
// ============================================================================

/// Global counter for gensym
static GENSYM_COUNTER: AtomicU64 = AtomicU64::new(0);

/// (gensym) or (gensym prefix) - generate unique symbol
pub(crate) fn builtin_gensym(args: &[KlujurVal]) -> Result<KlujurVal> {
    let prefix = match args.len() {
        0 => "G__",
        1 => match &args[0] {
            KlujurVal::String(s) => s.as_ref(),
            other => return Err(Error::type_error_in("gensym", "string", other.type_name())),
        },
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(0, 1),
                got: args.len(),
                name: Some("gensym".into()),
            });
        }
    };

    let n = GENSYM_COUNTER.fetch_add(1, Ordering::Relaxed);
    Ok(KlujurVal::Symbol(
        Symbol::new(&format!("{}{}", prefix, n)),
        None,
    ))
}

// ============================================================================
// Hashing
// ============================================================================

/// (hash x) - hash code for value
pub(crate) fn builtin_hash(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    if args.len() != 1 {
        return Err(Error::arity_named("hash", 1, args.len()));
    }

    let mut hasher = DefaultHasher::new();
    hash_val(&args[0], &mut hasher);
    Ok(KlujurVal::int(hasher.finish() as i64))
}

/// Helper to hash a KlujurVal
fn hash_val<H: std::hash::Hasher>(val: &KlujurVal, hasher: &mut H) {
    use std::hash::Hash;
    match val {
        KlujurVal::Nil => 0u8.hash(hasher),
        KlujurVal::Bool(b) => b.hash(hasher),
        KlujurVal::Int(n) => n.hash(hasher),
        KlujurVal::Float(f) => f.to_bits().hash(hasher),
        KlujurVal::Ratio(n, d) => {
            n.hash(hasher);
            d.hash(hasher);
        }
        KlujurVal::BigInt(n) => n.hash(hasher),
        KlujurVal::BigRatio(n, d) => {
            n.hash(hasher);
            d.hash(hasher);
        }
        KlujurVal::Char(c) => c.hash(hasher),
        KlujurVal::String(s) => s.hash(hasher),
        KlujurVal::Symbol(sym, _) => sym.hash(hasher),
        KlujurVal::Keyword(kw) => kw.hash(hasher),
        KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
            items.len().hash(hasher);
            for item in items.iter() {
                hash_val(item, hasher);
            }
        }
        KlujurVal::Map(map, _) => {
            map.len().hash(hasher);
            for (k, v) in map.iter() {
                hash_val(k, hasher);
                hash_val(v, hasher);
            }
        }
        KlujurVal::Set(set, _) => {
            set.len().hash(hasher);
            for item in set.iter() {
                hash_val(item, hasher);
            }
        }
        KlujurVal::Fn(f) => std::ptr::hash(f, hasher),
        KlujurVal::NativeFn(f) => f.name().hash(hasher),
        KlujurVal::Macro(f) => std::ptr::hash(f, hasher),
        KlujurVal::Var(v) => v.qualified_name().hash(hasher),
        KlujurVal::Atom(a) => std::ptr::hash(a, hasher),
        KlujurVal::Delay(d) => std::ptr::hash(d, hasher),
        KlujurVal::LazySeq(ls) => std::ptr::hash(ls, hasher),
        KlujurVal::Multimethod(mm) => std::ptr::hash(mm, hasher),
        KlujurVal::Hierarchy(h) => std::ptr::hash(h, hasher),
        KlujurVal::Reduced(v) => hash_val(v, hasher),
        KlujurVal::Volatile(v) => std::ptr::hash(v.as_ptr(), hasher),
        KlujurVal::Protocol(p) => std::ptr::hash(p, hasher),
        KlujurVal::Record(r) => {
            // Hash record type and values
            r.record_type.hash(hasher);
            r.record_ns.hash(hasher);
            for (k, v) in &r.values {
                k.hash(hasher);
                hash_val(v, hasher);
            }
        }
        KlujurVal::SortedMapBy(sm) => {
            // Hash sorted map entries (use default on re-entrancy - unlikely in hashing context)
            for (k, v) in sm.entries().unwrap_or_default().iter() {
                hash_val(k, hasher);
                hash_val(v, hasher);
            }
        }
        KlujurVal::SortedSetBy(ss) => {
            // Hash sorted set elements (use default on re-entrancy - unlikely in hashing context)
            for elem in ss.elements().unwrap_or_default().iter() {
                hash_val(elem, hasher);
            }
        }
        KlujurVal::Custom(c) => {
            // Hash custom type using its type name
            c.type_name().hash(hasher);
        }
        KlujurVal::Chunk(ch) => {
            // Hash chunk elements
            ch.len().hash(hasher);
            for elem in ch.iter() {
                hash_val(elem, hasher);
            }
        }
        KlujurVal::ChunkBuffer(cb) => {
            // Hash by pointer (mutable state)
            std::ptr::hash(cb, hasher);
        }
        KlujurVal::ChunkedSeq(cs) => {
            // Hash chunked seq by pointer (identity-based)
            std::ptr::hash(cs, hasher);
        }
        KlujurVal::Regex(r) => {
            // Hash regex by pattern string
            r.as_str().hash(hasher);
        }
    }
}
