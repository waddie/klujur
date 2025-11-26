// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Shared utility functions for the VM.

use klujur_parser::value::KlujurVal;

use crate::chunk::{HeapCell, HeapCellWrapper};
use crate::vm::{Result, RuntimeError};

/// Extract a HeapCell from a KlujurVal, returning an error if it's not a valid heap cell.
///
/// Used by LoadHeap, StoreHeap, LoadLocalHeap, and StoreLocalHeap operations.
pub fn get_heap_cell(val: &KlujurVal, context: &str) -> Result<HeapCell> {
    if let KlujurVal::Custom(custom) = val {
        if let Some(wrapper) = custom.downcast_ref::<HeapCellWrapper>() {
            Ok(wrapper.0.clone())
        } else {
            Err(RuntimeError::Internal(format!(
                "{}: value is not a HeapCell",
                context
            )))
        }
    } else {
        Err(RuntimeError::Internal(format!(
            "{}: value is not a Custom value",
            context
        )))
    }
}

/// Check function arity, returning an ArityError if mismatched.
///
/// For functions with rest parameters, `argc` must be >= `arity`.
/// For fixed-arity functions, `argc` must equal `arity`.
/// Multi-arity functions skip this check (handled via ArityDispatch opcode).
pub fn check_arity(argc: usize, arity: usize, has_rest: bool, is_multi_arity: bool) -> Result<()> {
    if is_multi_arity {
        return Ok(());
    }

    if has_rest {
        if argc < arity {
            return Err(RuntimeError::ArityError {
                expected: arity,
                got: argc,
            });
        }
    } else if argc != arity {
        return Err(RuntimeError::ArityError {
            expected: arity,
            got: argc,
        });
    }

    Ok(())
}

/// Collect extra arguments into a rest list.
///
/// Returns `Some(list)` if there's a rest parameter, `None` otherwise.
/// For multi-arity functions, returns `None` (rest handling is done differently).
pub fn build_rest_list(
    args: impl Iterator<Item = KlujurVal>,
    arity: usize,
    argc: usize,
    has_rest: bool,
    is_multi_arity: bool,
) -> Option<KlujurVal> {
    if is_multi_arity {
        return None;
    }

    if has_rest {
        if argc > arity {
            // Collect extra args into a list
            let rest_items: Vec<_> = args.skip(arity).collect();
            Some(KlujurVal::list(rest_items))
        } else {
            // No extra args, return empty list for rest parameter
            Some(KlujurVal::list(vec![]))
        }
    } else {
        None
    }
}

/// Get the type name for a KlujurVal (for error messages).
pub fn type_name(val: &KlujurVal) -> &'static str {
    match val {
        KlujurVal::Nil => "nil",
        KlujurVal::Bool(_) => "boolean",
        KlujurVal::Int(_) => "integer",
        KlujurVal::BigInt(_) => "bigint",
        KlujurVal::Float(_) => "float",
        KlujurVal::Ratio(..) => "ratio",
        KlujurVal::BigRatio(..) => "bigratio",
        KlujurVal::Char(_) => "char",
        KlujurVal::String(_) => "string",
        KlujurVal::Symbol(..) => "symbol",
        KlujurVal::Keyword(_) => "keyword",
        KlujurVal::List(..) => "list",
        KlujurVal::Vector(..) => "vector",
        KlujurVal::Map(..) => "map",
        KlujurVal::Set(..) => "set",
        KlujurVal::Fn(_) => "function",
        KlujurVal::NativeFn(_) => "native-function",
        KlujurVal::Macro(_) => "macro",
        KlujurVal::Var(_) => "var",
        KlujurVal::Atom(_) => "atom",
        KlujurVal::Delay(_) => "delay",
        KlujurVal::LazySeq(_) => "lazy-seq",
        KlujurVal::Volatile(_) => "volatile",
        KlujurVal::Multimethod(_) => "multimethod",
        KlujurVal::Protocol(_) => "protocol",
        KlujurVal::Hierarchy(_) => "hierarchy",
        KlujurVal::Record(_) => "record",
        KlujurVal::Reduced(_) => "reduced",
        KlujurVal::SortedMapBy(_) => "sorted-map-by",
        KlujurVal::SortedSetBy(_) => "sorted-set-by",
        KlujurVal::Custom(_) => "custom",
        KlujurVal::Chunk(_) => "chunk",
        KlujurVal::ChunkBuffer(_) => "chunk-buffer",
        KlujurVal::ChunkedSeq(_) => "chunked-seq",
        KlujurVal::Regex(_) => "regex",
    }
}

/// Check if a value is falsy (nil or false).
pub fn is_falsy(val: &KlujurVal) -> bool {
    matches!(val, KlujurVal::Nil | KlujurVal::Bool(false))
}
