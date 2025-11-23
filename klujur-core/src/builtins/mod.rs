// klujur-core - Built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Built-in functions for Klujur.

// Allow mutable key types - KlujurVal has interior mutability for Vars by design
#![allow(clippy::mutable_key_type)]

mod additional_higher_order;
mod additional_predicates;
mod arithmetic;
mod atoms;
mod bitwise;
mod collection_constructors;
mod collection_utils;
mod collections;
mod comparison;
mod eager_sequences;
mod exceptions;
mod higher_order;
mod io;
mod laziness;
mod logic;
mod metadata;
mod multimethods;
mod predicates;
mod random;
mod sequences;
mod strings;
mod transducers;
mod type_checks;
mod vars;

use klujur_parser::{KlujurVal, Symbol};

use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::{apply, make_native_fn};

use additional_higher_order::{
    builtin_complement, builtin_every_pred, builtin_fnil, builtin_juxt, builtin_reduce_kv,
    builtin_some_fn,
};
use additional_predicates::{
    builtin_associative_p, builtin_compare, builtin_counted_p, builtin_false_p,
    builtin_identical_p, builtin_indexed_p, builtin_not_empty, builtin_num_eq,
    builtin_reversible_p, builtin_seqable_p, builtin_sequential_p, builtin_sorted_p,
    builtin_true_p,
};
use arithmetic::{
    builtin_abs, builtin_add, builtin_dec, builtin_div, builtin_even_p, builtin_inc, builtin_max,
    builtin_min, builtin_mod, builtin_mul, builtin_neg_p, builtin_odd_p, builtin_pos_p,
    builtin_quot, builtin_rem, builtin_sub, builtin_zero_p,
};
use atoms::{
    builtin_add_watch, builtin_atom, builtin_atom_p, builtin_compare_and_set,
    builtin_get_validator, builtin_remove_watch, builtin_reset, builtin_reset_vals,
    builtin_set_validator, builtin_swap, builtin_swap_vals,
};
use bitwise::{
    builtin_bit_and, builtin_bit_and_not, builtin_bit_clear, builtin_bit_flip, builtin_bit_not,
    builtin_bit_or, builtin_bit_set, builtin_bit_shift_left, builtin_bit_shift_right,
    builtin_bit_test, builtin_bit_xor, builtin_unsigned_bit_shift_right, require_int,
};
use collection_constructors::{
    builtin_hash_map, builtin_hash_set, builtin_list_star, builtin_set, builtin_sorted_map,
    builtin_sorted_set, builtin_vec, builtin_zipmap,
};
use collection_utils::{
    builtin_assoc_in, builtin_contains_p, builtin_disj, builtin_empty, builtin_find,
    builtin_get_in, builtin_keys, builtin_merge, builtin_merge_with, builtin_peek, builtin_pop,
    builtin_select_keys, builtin_update, builtin_update_in, builtin_update_keys,
    builtin_update_vals, builtin_vals,
};
use collections::{
    builtin_assoc, builtin_conj, builtin_dissoc, builtin_get, builtin_list, builtin_vector,
};
use comparison::{builtin_eq, builtin_ge, builtin_gt, builtin_le, builtin_lt, builtin_not_eq};
use eager_sequences::{
    builtin_ffirst, builtin_fnext, builtin_frequencies, builtin_group_by, builtin_nfirst,
    builtin_nnext, builtin_rseq, builtin_sort, builtin_sort_by,
};
use exceptions::{builtin_ex_data, builtin_ex_info, builtin_ex_message};
use higher_order::{
    builtin_apply, builtin_comp, builtin_constantly, builtin_every_p, builtin_filter,
    builtin_identity, builtin_map, builtin_not_any_p, builtin_not_every_p, builtin_partial,
    builtin_reduce, builtin_remove, builtin_some,
};
use io::{
    builtin_format, builtin_get_print_length, builtin_pr_str, builtin_print, builtin_println,
    builtin_read_string, builtin_set_print_length, builtin_slurp, builtin_spit, builtin_str,
};
use laziness::{
    builtin_delay_p, builtin_doall, builtin_dorun, builtin_force, builtin_lazy_seq_p,
    builtin_memoize, builtin_realized_p,
};
use logic::{builtin_boolean, builtin_not};
use metadata::{
    builtin_alter_meta, builtin_meta, builtin_reset_meta, builtin_vary_meta, builtin_with_meta,
};
use multimethods::{
    builtin_ancestors, builtin_descendants, builtin_get_method, builtin_isa,
    builtin_make_hierarchy, builtin_methods, builtin_parents, builtin_prefer_method,
    builtin_prefers, builtin_remove_all_methods, builtin_remove_method,
};
use predicates::{
    builtin_boolean_p, builtin_coll_p, builtin_float_p, builtin_fn_p, builtin_integer_p,
    builtin_keyword_p, builtin_list_p, builtin_map_p, builtin_nil_p, builtin_number_p,
    builtin_seq_p, builtin_set_p, builtin_some_p, builtin_string_p, builtin_symbol_p,
    builtin_vector_p,
};
use random::{
    builtin_gensym, builtin_hash, builtin_rand, builtin_rand_int, builtin_rand_nth, builtin_shuffle,
};
use sequences::{
    builtin_butlast, builtin_concat, builtin_cons, builtin_count, builtin_drop, builtin_empty_p,
    builtin_first, builtin_into, builtin_last, builtin_mapcat, builtin_next, builtin_nth,
    builtin_partition, builtin_range, builtin_repeat, builtin_rest, builtin_reverse,
    builtin_second, builtin_seq, builtin_take,
};
use strings::{builtin_keyword, builtin_name, builtin_namespace, builtin_subs, builtin_symbol};
use transducers::{
    builtin_ensure_reduced, builtin_reduced, builtin_reduced_p, builtin_transduce,
    builtin_unreduced, builtin_volatile, builtin_volatile_p, builtin_vreset, builtin_vswap,
};
use type_checks::{builtin_extends_p, builtin_satisfies_p, builtin_type};
use vars::{
    builtin_bound_p, builtin_deref, builtin_thread_bound_p, builtin_var_get, builtin_var_p,
    builtin_var_set,
};

/// Register all built-in functions in the given environment.
pub fn register_builtins(env: &Env) {
    // Arithmetic
    env.define_native("+", builtin_add);
    env.define_native("-", builtin_sub);
    env.define_native("*", builtin_mul);
    env.define_native("/", builtin_div);
    env.define_native("quot", builtin_quot);
    env.define_native("rem", builtin_rem);
    env.define_native("mod", builtin_mod);
    env.define_native("inc", builtin_inc);
    env.define_native("dec", builtin_dec);
    env.define_native("max", builtin_max);
    env.define_native("min", builtin_min);
    env.define_native("abs", builtin_abs);

    // Numeric predicates
    env.define_native("even?", builtin_even_p);
    env.define_native("odd?", builtin_odd_p);
    env.define_native("pos?", builtin_pos_p);
    env.define_native("neg?", builtin_neg_p);
    env.define_native("zero?", builtin_zero_p);

    // Comparison
    env.define_native("=", builtin_eq);
    env.define_native("<", builtin_lt);
    env.define_native(">", builtin_gt);
    env.define_native("<=", builtin_le);
    env.define_native(">=", builtin_ge);
    env.define_native("not=", builtin_not_eq);

    // Type predicates
    env.define_native("nil?", builtin_nil_p);
    env.define_native("some?", builtin_some_p);
    env.define_native("boolean?", builtin_boolean_p);
    env.define_native("number?", builtin_number_p);
    env.define_native("integer?", builtin_integer_p);
    env.define_native("float?", builtin_float_p);
    env.define_native("string?", builtin_string_p);
    env.define_native("symbol?", builtin_symbol_p);
    env.define_native("keyword?", builtin_keyword_p);
    env.define_native("list?", builtin_list_p);
    env.define_native("vector?", builtin_vector_p);
    env.define_native("map?", builtin_map_p);
    env.define_native("set?", builtin_set_p);
    env.define_native("fn?", builtin_fn_p);
    env.define_native("coll?", builtin_coll_p);
    env.define_native("seq?", builtin_seq_p);
    env.define_native("var?", builtin_var_p);
    env.define_native("seqable?", builtin_seqable_p);
    env.define_native("sequential?", builtin_sequential_p);
    env.define_native("sorted?", builtin_sorted_p);
    env.define_native("counted?", builtin_counted_p);
    env.define_native("reversible?", builtin_reversible_p);
    env.define_native("associative?", builtin_associative_p);
    env.define_native("indexed?", builtin_indexed_p);

    // Vars
    env.define_native("deref", builtin_deref);

    // Atoms
    env.define_native("atom", builtin_atom);
    env.define_native("atom?", builtin_atom_p);
    env.define_native("reset!", builtin_reset);
    env.define_native("swap!", builtin_swap);
    env.define_native("swap-vals!", builtin_swap_vals);
    env.define_native("reset-vals!", builtin_reset_vals);
    env.define_native("compare-and-set!", builtin_compare_and_set);
    env.define_native("add-watch", builtin_add_watch);
    env.define_native("remove-watch", builtin_remove_watch);
    env.define_native("set-validator!", builtin_set_validator);
    env.define_native("get-validator", builtin_get_validator);

    // Delays and Lazy Sequences
    env.define_native("delay?", builtin_delay_p);
    env.define_native("force", builtin_force);
    env.define_native("realized?", builtin_realized_p);
    env.define_native("lazy-seq?", builtin_lazy_seq_p);
    env.define_native("doall", builtin_doall);
    env.define_native("dorun", builtin_dorun);

    // Memoization
    env.define_native("memoize", builtin_memoize);

    // Sequences
    env.define_native("first", builtin_first);
    env.define_native("rest", builtin_rest);
    env.define_native("next", builtin_next);
    env.define_native("second", builtin_second);
    env.define_native("last", builtin_last);
    env.define_native("butlast", builtin_butlast);
    env.define_native("cons", builtin_cons);
    env.define_native("count", builtin_count);
    env.define_native("nth", builtin_nth);
    env.define_native("empty?", builtin_empty_p);
    env.define_native("take*", builtin_take);
    env.define_native("drop*", builtin_drop);
    env.define_native("concat", builtin_concat);
    env.define_native("mapcat*", builtin_mapcat);
    env.define_native("partition", builtin_partition);
    env.define_native("reverse", builtin_reverse);
    env.define_native("range", builtin_range);
    env.define_native("repeat", builtin_repeat);
    env.define_native("into", builtin_into);
    env.define_native("seq", builtin_seq);

    // Logic
    env.define_native("not", builtin_not);
    env.define_native("boolean", builtin_boolean);

    // Collections
    env.define_native("list", builtin_list);
    env.define_native("vector", builtin_vector);
    env.define_native("get", builtin_get);
    env.define_native("assoc", builtin_assoc);
    env.define_native("dissoc", builtin_dissoc);
    env.define_native("conj", builtin_conj);

    // Misc
    env.define_native("str", builtin_str);
    env.define_native("pr-str", builtin_pr_str);
    env.define_native("print", builtin_print);
    env.define_native("println", builtin_println);
    env.define_native("type", builtin_type);
    env.define_native("satisfies?", builtin_satisfies_p);
    env.define_native("extends?", builtin_extends_p);
    env.define_native("identity", builtin_identity);
    env.define_native("set-print-length!", builtin_set_print_length);
    env.define_native("get-print-length", builtin_get_print_length);

    // Higher-order functions
    env.define_native("apply", builtin_apply);
    env.define_native("map*", builtin_map);
    env.define_native("filter*", builtin_filter);
    env.define_native("remove*", builtin_remove);
    env.define_native("reduce", builtin_reduce);
    env.define_native("comp", builtin_comp);
    env.define_native("partial", builtin_partial);
    env.define_native("constantly", builtin_constantly);
    env.define_native("every?", builtin_every_p);
    env.define_native("some", builtin_some);
    env.define_native("not-any?", builtin_not_any_p);
    env.define_native("not-every?", builtin_not_every_p);

    // Exceptions
    env.define_native("ex-info", builtin_ex_info);
    env.define_native("ex-message", builtin_ex_message);
    env.define_native("ex-data", builtin_ex_data);

    // Dynamic bindings
    env.define_native("bound?", builtin_bound_p);
    env.define_native("thread-bound?", builtin_thread_bound_p);
    env.define_native("var-get", builtin_var_get);
    env.define_native("var-set", builtin_var_set);

    // String/Symbol/Keyword operations
    env.define_native("name", builtin_name);
    env.define_native("namespace", builtin_namespace);
    env.define_native("symbol", builtin_symbol);
    env.define_native("keyword", builtin_keyword);
    env.define_native("subs", builtin_subs);

    // Additional predicates
    env.define_native("true?", builtin_true_p);
    env.define_native("false?", builtin_false_p);
    env.define_native("==", builtin_num_eq);
    env.define_native("compare", builtin_compare);
    env.define_native("identical?", builtin_identical_p);
    env.define_native("not-empty", builtin_not_empty);
    env.define_native("seqable?", builtin_seqable_p);
    env.define_native("sequential?", builtin_sequential_p);
    env.define_native("sorted?", builtin_sorted_p);
    env.define_native("counted?", builtin_counted_p);
    env.define_native("reversible?", builtin_reversible_p);
    env.define_native("associative?", builtin_associative_p);
    env.define_native("indexed?", builtin_indexed_p);

    // Collection utilities
    env.define_native("keys", builtin_keys);
    env.define_native("vals", builtin_vals);
    env.define_native("find", builtin_find);
    env.define_native("contains?", builtin_contains_p);
    env.define_native("select-keys", builtin_select_keys);
    env.define_native("merge", builtin_merge);
    env.define_native("merge-with", builtin_merge_with);
    env.define_native("get-in", builtin_get_in);
    env.define_native("assoc-in", builtin_assoc_in);
    env.define_native("update", builtin_update);
    env.define_native("update-in", builtin_update_in);
    env.define_native("update-keys", builtin_update_keys);
    env.define_native("update-vals", builtin_update_vals);
    env.define_native("peek", builtin_peek);
    env.define_native("pop", builtin_pop);
    env.define_native("disj", builtin_disj);
    env.define_native("empty", builtin_empty);

    // Collection constructors
    env.define_native("vec", builtin_vec);
    env.define_native("set", builtin_set);
    env.define_native("hash-map", builtin_hash_map);
    env.define_native("hash-set", builtin_hash_set);
    env.define_native("sorted-map", builtin_sorted_map);
    env.define_native("sorted-set", builtin_sorted_set);
    env.define_native("list*", builtin_list_star);
    env.define_native("zipmap", builtin_zipmap);

    // Bitwise operations
    env.define_native("bit-and", builtin_bit_and);
    env.define_native("bit-or", builtin_bit_or);
    env.define_native("bit-xor", builtin_bit_xor);
    env.define_native("bit-not", builtin_bit_not);
    env.define_native("bit-and-not", builtin_bit_and_not);
    env.define_native("bit-shift-left", builtin_bit_shift_left);
    env.define_native("bit-shift-right", builtin_bit_shift_right);
    env.define_native("unsigned-bit-shift-right", builtin_unsigned_bit_shift_right);
    env.define_native("bit-set", builtin_bit_set);
    env.define_native("bit-clear", builtin_bit_clear);
    env.define_native("bit-flip", builtin_bit_flip);
    env.define_native("bit-test", builtin_bit_test);

    // Additional higher-order functions
    env.define_native("reduce-kv", builtin_reduce_kv);
    env.define_native("juxt", builtin_juxt);
    env.define_native("complement", builtin_complement);
    env.define_native("fnil", builtin_fnil);
    env.define_native("some-fn", builtin_some_fn);
    env.define_native("every-pred", builtin_every_pred);

    // Eager sequence functions
    env.define_native("sort", builtin_sort);
    env.define_native("sort-by", builtin_sort_by);
    env.define_native("frequencies", builtin_frequencies);
    env.define_native("group-by", builtin_group_by);
    env.define_native("ffirst", builtin_ffirst);
    env.define_native("nfirst", builtin_nfirst);
    env.define_native("nnext", builtin_nnext);
    env.define_native("fnext", builtin_fnext);
    env.define_native("rseq", builtin_rseq);

    // Random & utilities
    env.define_native("rand", builtin_rand);
    env.define_native("rand-int", builtin_rand_int);
    env.define_native("rand-nth", builtin_rand_nth);
    env.define_native("shuffle", builtin_shuffle);
    env.define_native("gensym", builtin_gensym);
    env.define_native("hash", builtin_hash);

    // Metadata
    env.define_native("meta", builtin_meta);
    env.define_native("with-meta", builtin_with_meta);
    env.define_native("vary-meta", builtin_vary_meta);
    env.define_native("alter-meta!", builtin_alter_meta);
    env.define_native("reset-meta!", builtin_reset_meta);

    // I/O & evaluation
    env.define_native("read-string", builtin_read_string);
    env.define_native("slurp", builtin_slurp);
    env.define_native("spit", builtin_spit);
    env.define_native("format", builtin_format);

    // Multimethods
    env.define_native("methods", builtin_methods);
    env.define_native("get-method", builtin_get_method);
    env.define_native("remove-method", builtin_remove_method);
    env.define_native("prefer-method", builtin_prefer_method);
    env.define_native("prefers", builtin_prefers);
    env.define_native("remove-all-methods", builtin_remove_all_methods);

    // Hierarchies
    env.define_native("make-hierarchy", builtin_make_hierarchy);
    env.define_native("isa?", builtin_isa);
    env.define_native("parents", builtin_parents);
    env.define_native("ancestors", builtin_ancestors);
    env.define_native("descendants", builtin_descendants);

    // Transducers - Reduced type
    env.define_native("reduced", builtin_reduced);
    env.define_native("reduced?", builtin_reduced_p);
    env.define_native("unreduced", builtin_unreduced);
    env.define_native("ensure-reduced", builtin_ensure_reduced);

    // Volatiles
    env.define_native("volatile!", builtin_volatile);
    env.define_native("volatile?", builtin_volatile_p);
    env.define_native("vreset!", builtin_vreset);
    env.define_native("vswap!", builtin_vswap);

    // Transducers - execution
    env.define_native("transduce", builtin_transduce);
}

/// Helper trait to define native functions more easily.
pub trait EnvExt {
    fn define_native(&self, name: &'static str, func: fn(&[KlujurVal]) -> Result<KlujurVal>);
}

impl EnvExt for Env {
    fn define_native(&self, name: &'static str, func: fn(&[KlujurVal]) -> Result<KlujurVal>) {
        let native = make_native_fn(name, func);
        self.define(Symbol::new(name), KlujurVal::NativeFn(native));
    }
}

// ============================================================================
// Shared Helpers
// ============================================================================

pub(crate) fn compare_numbers(a: &KlujurVal, b: &KlujurVal) -> Result<std::cmp::Ordering> {
    match (a, b) {
        (KlujurVal::Int(x), KlujurVal::Int(y)) => Ok(x.cmp(y)),
        (KlujurVal::Float(x), KlujurVal::Float(y)) => x
            .partial_cmp(y)
            .ok_or_else(|| Error::EvalError("Cannot compare NaN".into())),
        (KlujurVal::Int(x), KlujurVal::Float(y)) => {
            let fx = *x as f64;
            fx.partial_cmp(y)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))
        }
        (KlujurVal::Float(x), KlujurVal::Int(y)) => {
            let fy = *y as f64;
            x.partial_cmp(&fy)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))
        }
        (a, b) => Err(Error::type_error_in(
            "comparison",
            "number",
            if !matches!(a, KlujurVal::Int(_) | KlujurVal::Float(_)) {
                a.type_name()
            } else {
                b.type_name()
            },
        )),
    }
}

// ============================================================================
// Sequences
// ============================================================================

use klujur_parser::{KlujurLazySeq, SeqResult};

/// Force a lazy sequence and return its SeqResult.
/// If already realized, returns the cached result.
pub(crate) fn force_lazy_seq(ls: &KlujurLazySeq) -> Result<SeqResult> {
    // Check if already realized
    if let Some(result) = ls.get_cached() {
        return Ok(result);
    }

    // Get the thunk and evaluate it
    if let Some(thunk) = ls.get_thunk() {
        let val = apply(&KlujurVal::Fn(thunk), &[])?;

        // Convert the result to a SeqResult
        let result = match val {
            KlujurVal::Nil => SeqResult::Empty,
            KlujurVal::List(items, _) if items.is_empty() => SeqResult::Empty,
            KlujurVal::List(items, _) => {
                let first = items.front().cloned().unwrap_or(KlujurVal::Nil);
                let rest = KlujurVal::list(items.iter().skip(1).cloned().collect());
                SeqResult::Cons(first, rest)
            }
            KlujurVal::Vector(items, _) if items.is_empty() => SeqResult::Empty,
            KlujurVal::Vector(items, _) => {
                let first = items.front().cloned().unwrap_or(KlujurVal::Nil);
                let rest = KlujurVal::list(items.iter().skip(1).cloned().collect());
                SeqResult::Cons(first, rest)
            }
            // If the body returns another lazy seq, we return its result
            KlujurVal::LazySeq(inner_ls) => force_lazy_seq(&inner_ls)?,
            other => {
                // Check if it's a cons-like structure - just treat non-empty as first element
                return Err(Error::type_error_in(
                    "lazy-seq body",
                    "nil or sequence",
                    other.type_name(),
                ));
            }
        };

        ls.set_realized(result.clone());
        Ok(result)
    } else {
        // Should not happen - if not cached, must have thunk
        Err(Error::syntax("force", "lazy-seq in invalid state"))
    }
}

// Sequence functions moved to sequences.rs

// Old sequence functions removed - see sequences.rs

/// Helper to convert a value to a sequence of values
pub(crate) fn to_seq(val: &KlujurVal) -> Result<Vec<KlujurVal>> {
    match val {
        KlujurVal::Nil => Ok(Vec::new()),
        KlujurVal::List(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Vector(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::Set(items, _) => Ok(items.iter().cloned().collect()),
        KlujurVal::String(s) => Ok(s.chars().map(KlujurVal::char).collect()),
        KlujurVal::LazySeq(ls) => {
            // Force the lazy seq and collect all elements
            let mut result = Vec::new();
            let mut current = KlujurVal::LazySeq(ls.clone());
            loop {
                match &current {
                    KlujurVal::Nil => break,
                    KlujurVal::List(items, _) if items.is_empty() => break,
                    KlujurVal::List(items, _) => {
                        result.extend(items.iter().cloned());
                        break;
                    }
                    KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => break,
                        SeqResult::Cons(first, rest) => {
                            result.push(first);
                            current = rest;
                        }
                    },
                    _ => break,
                }
            }
            Ok(result)
        }
        other => Err(Error::type_error_in("seq", "seqable", other.type_name())),
    }
}
