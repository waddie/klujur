// klujur-core - Chunked sequence built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Chunked sequence operations for efficient batch processing.
//!
//! Chunked sequences process elements in batches of 32 (by default),
//! reducing the overhead of lazy evaluation for large sequences.

use klujur_parser::{
    KlujurChunk, KlujurChunkBuffer, KlujurChunkedSeq, KlujurVal, NativeChunkThunk,
};

use crate::error::{Error, Result};
use crate::eval::apply;

use super::sequences::CHUNK_SIZE;

// ============================================================================
// Forcing chunked rest
// ============================================================================

/// Force the rest thunk of a chunked sequence and return the rest as a KlujurVal.
///
/// This is analogous to `force_lazy_seq` but for chunked sequences.
/// Returns:
/// - Nil (end of sequence)
/// - A seqable value (ChunkedSeq, LazySeq, List, etc.)
pub(crate) fn force_chunked_rest(cs: &KlujurChunkedSeq) -> Result<KlujurVal> {
    // Check if already realized
    if let Some(cached) = cs.get_cached_rest() {
        return Ok(cached);
    }

    // Try Klujur function thunk first
    if let Some(thunk) = cs.get_rest_thunk() {
        let val = apply(&KlujurVal::Fn(thunk), &[])?;
        // Cache and return the result (can be any seqable or Nil)
        cs.set_rest_realized(val.clone());
        return Ok(val);
    }

    // Try native thunk
    if let Some(native_thunk) = cs.get_native_rest_thunk() {
        let val = match native_thunk {
            NativeChunkThunk::Closure(f) => f().map_err(Error::EvalError)?,
            NativeChunkThunk::Range { start, end, step } => {
                // Compute range chunk directly - no recursion, no closures
                compute_range_chunk(start, end, step)
            }
        };
        // Cache and return the result (can be any seqable or Nil)
        cs.set_rest_realized(val.clone());
        return Ok(val);
    }

    // Should not happen - if not cached, must have some thunk
    Err(Error::syntax("force", "chunked-seq in invalid state"))
}

/// Compute the next chunk for a range - pure function, no closures, no recursion.
fn compute_range_chunk(start: i64, end: i64, step: i64) -> KlujurVal {
    // Check if we've reached the end
    let at_end = if step > 0 { start >= end } else { start <= end };
    if at_end {
        return KlujurVal::Nil;
    }

    // Build the chunk
    let chunk = build_range_chunk(start, end, step);
    if chunk.is_empty() {
        return KlujurVal::Nil;
    }

    // Calculate next chunk start
    let next_start = start + (chunk.len() as i64) * step;

    // Create next thunk as Range variant - NO CLOSURE ALLOCATION
    let rest_thunk = NativeChunkThunk::Range {
        start: next_start,
        end,
        step,
    };

    KlujurVal::ChunkedSeq(KlujurChunkedSeq::new_native(chunk, rest_thunk))
}

/// Build a chunk of range values starting from `start`.
fn build_range_chunk(start: i64, end: i64, step: i64) -> KlujurChunk {
    let mut elements = Vec::with_capacity(CHUNK_SIZE);
    let mut i = start;

    if step > 0 {
        while i < end && elements.len() < CHUNK_SIZE {
            elements.push(KlujurVal::int(i));
            i += step;
        }
    } else {
        while i > end && elements.len() < CHUNK_SIZE {
            elements.push(KlujurVal::int(i));
            i += step;
        }
    }

    KlujurChunk::new(elements)
}

// ============================================================================
// Chunk operations
// ============================================================================

/// (chunk-first cs) - Get the current chunk from a chunked sequence.
pub(crate) fn builtin_chunk_first(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk-first", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::ChunkedSeq(cs) => Ok(KlujurVal::Chunk(cs.chunk().clone())),
        other => Err(Error::type_error_in(
            "chunk-first",
            "chunked-seq",
            other.type_name(),
        )),
    }
}

/// (chunk-rest cs) - Get the rest of a chunked sequence (forces the thunk).
/// Returns an empty list if at the end.
pub(crate) fn builtin_chunk_rest(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk-rest", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::ChunkedSeq(cs) => {
            let rest = force_chunked_rest(cs)?;
            if rest == KlujurVal::Nil {
                Ok(KlujurVal::list(vec![])) // Empty list like Clojure's chunkedMore()
            } else {
                Ok(rest)
            }
        }
        other => Err(Error::type_error_in(
            "chunk-rest",
            "chunked-seq",
            other.type_name(),
        )),
    }
}

/// (chunk-next cs) - Get the next chunked sequence (forces the thunk).
/// Returns nil if at the end.
pub(crate) fn builtin_chunk_next(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk-next", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::ChunkedSeq(cs) => Ok(force_chunked_rest(cs)?),
        other => Err(Error::type_error_in(
            "chunk-next",
            "chunked-seq",
            other.type_name(),
        )),
    }
}

/// (chunk-cons chunk rest) - Create a chunked sequence from a chunk and rest.
/// If the chunk is empty, returns the rest.
pub(crate) fn builtin_chunk_cons(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("chunk-cons", 2, args.len()));
    }
    let chunk = match &args[0] {
        KlujurVal::Chunk(c) => c.clone(),
        other => {
            return Err(Error::type_error_in(
                "chunk-cons",
                "chunk",
                other.type_name(),
            ));
        }
    };

    // If chunk is empty, return rest
    if chunk.is_empty() {
        return Ok(args[1].clone());
    }

    // Create ChunkedSeq with the rest as-is (any seqable value)
    // The rest can be ChunkedSeq, LazySeq, List, Nil, etc.
    Ok(KlujurVal::ChunkedSeq(KlujurChunkedSeq::with_rest(
        chunk,
        args[1].clone(),
    )))
}

// ============================================================================
// Predicates
// ============================================================================

/// (chunked-seq? x) - Returns true if x is a chunked sequence.
pub(crate) fn builtin_chunked_seq_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunked-seq?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::ChunkedSeq(_))))
}

/// (chunk? x) - Returns true if x is a chunk.
pub(crate) fn builtin_chunk_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Chunk(_))))
}

// ============================================================================
// ChunkBuffer operations
// ============================================================================

/// (chunk-buffer n) - Create a chunk buffer with capacity n.
pub(crate) fn builtin_chunk_buffer(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk-buffer", 1, args.len()));
    }
    let capacity = match &args[0] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => {
            return Err(Error::syntax(
                "chunk-buffer",
                "capacity must be non-negative",
            ));
        }
        other => {
            return Err(Error::type_error_in(
                "chunk-buffer",
                "integer",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::ChunkBuffer(KlujurChunkBuffer::new(capacity)))
}

/// (chunk-append buf val) - Append a value to a chunk buffer. Returns the buffer.
pub(crate) fn builtin_chunk_append(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("chunk-append", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::ChunkBuffer(buf) => {
            buf.add(args[1].clone());
            Ok(args[0].clone())
        }
        other => Err(Error::type_error_in(
            "chunk-append",
            "chunk-buffer",
            other.type_name(),
        )),
    }
}

/// (chunk buf) - Finalize a chunk buffer into a chunk.
pub(crate) fn builtin_chunk(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::ChunkBuffer(buf) => Ok(KlujurVal::Chunk(buf.to_chunk())),
        other => Err(Error::type_error_in(
            "chunk",
            "chunk-buffer",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Chunk access
// ============================================================================

/// (chunk-count chunk) - Returns the number of elements in a chunk.
pub(crate) fn builtin_chunk_count(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("chunk-count", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Chunk(c) => Ok(KlujurVal::Int(c.len() as i64)),
        other => Err(Error::type_error_in(
            "chunk-count",
            "chunk",
            other.type_name(),
        )),
    }
}

/// (chunk-nth chunk n) - Get the nth element of a chunk.
pub(crate) fn builtin_chunk_nth(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("chunk-nth", 2, args.len()));
    }
    let chunk = match &args[0] {
        KlujurVal::Chunk(c) => c,
        other => {
            return Err(Error::type_error_in(
                "chunk-nth",
                "chunk",
                other.type_name(),
            ));
        }
    };
    let n = match &args[1] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => return Err(Error::syntax("chunk-nth", "index must be non-negative")),
        other => {
            return Err(Error::type_error_in(
                "chunk-nth",
                "integer",
                other.type_name(),
            ));
        }
    };
    chunk.nth(n).cloned().ok_or_else(|| {
        Error::syntax(
            "chunk-nth",
            format!(
                "index {} out of bounds for chunk of length {}",
                n,
                chunk.len()
            ),
        )
    })
}
