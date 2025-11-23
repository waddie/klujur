// klujur-core - Special forms
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Special forms for the Klujur evaluator.

pub mod control;
pub mod threading;
pub mod utility;

pub use control::{eval_and, eval_cond, eval_if_not, eval_or, eval_when, eval_when_not};
pub use threading::{eval_as_thread, eval_thread_first, eval_thread_last};
pub use utility::{eval_eval, eval_load_file, eval_load_string, eval_time};
