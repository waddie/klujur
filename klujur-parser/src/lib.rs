// klujur-parser - Lexer and parser for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! # klujur-parser
//!
//! Lexer and parser for the Klujur programming language.
//! Produces `KlujurVal` AST from source code strings.

pub mod hierarchy;
pub mod keyword;
pub mod lexer;
pub mod parser;
pub mod symbol;
pub mod value;

pub use hierarchy::KlujurHierarchy;
pub use im::{OrdMap, OrdSet, Vector};
pub use keyword::Keyword;
pub use lexer::Lexer;
pub use num_bigint::BigInt;
pub use num_traits::ToPrimitive;
pub use parser::Parser;
pub use symbol::Symbol;
pub use value::{
    ChunkedRestState, CustomType, FnArity, KlujurAtom, KlujurChunk, KlujurChunkBuffer,
    KlujurChunkedSeq, KlujurCustom, KlujurDelay, KlujurFn, KlujurLazySeq, KlujurMultimethod,
    KlujurNativeFn, KlujurProtocol, KlujurRegex, KlujurSortedMapBy, KlujurSortedSetBy, KlujurVal,
    KlujurVar, KlujurVolatile, LazySeqState, Meta, MethodSignature, NativeChunkThunk, Protocol,
    RecordDef, RecordInstance, SeqResult, TypeImpl, TypeKey, get_print_length, set_print_length,
};
