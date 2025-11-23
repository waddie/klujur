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
pub mod collection_constructors;
mod collection_utils;
mod collections;
pub mod comparators;
mod comparison;
mod datetime;
mod eager_sequences;
mod exceptions;
mod higher_order;
mod io;
mod laziness;
mod logic;
mod math;
mod metadata;
mod multimethods;
mod predicates;
mod random;
mod sequences;
mod strings;
mod transducers;
mod type_checks;
mod vars;

use klujur_parser::KlujurVal;

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
    builtin_abs, builtin_add, builtin_dec, builtin_div, builtin_double, builtin_even_p,
    builtin_inc, builtin_int, builtin_max, builtin_min, builtin_mod, builtin_mul, builtin_neg_p,
    builtin_odd_p, builtin_pos_p, builtin_quot, builtin_rem, builtin_sub, builtin_zero_p,
};
use atoms::{
    builtin_add_watch, builtin_atom, builtin_atom_p, builtin_compare_and_set,
    builtin_get_validator, builtin_remove_watch, builtin_reset, builtin_reset_vals,
    builtin_set_validator,
};
use bitwise::{
    builtin_bit_and, builtin_bit_and_not, builtin_bit_clear, builtin_bit_flip, builtin_bit_not,
    builtin_bit_or, builtin_bit_set, builtin_bit_shift_left, builtin_bit_shift_right,
    builtin_bit_test, builtin_bit_xor, builtin_unsigned_bit_shift_right, require_int,
};
use collection_constructors::{
    builtin_hash_map, builtin_hash_set, builtin_list_star, builtin_set, builtin_sorted_map,
    builtin_sorted_map_by, builtin_sorted_set, builtin_sorted_set_by, builtin_vec, builtin_zipmap,
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
use datetime::{
    builtin_now_micros, builtin_now_millis, builtin_now_nanos, builtin_now_secs,
    builtin_system_time,
};
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
    builtin_exit, builtin_flush, builtin_format, builtin_get_print_length, builtin_getenv,
    builtin_pr_str, builtin_print, builtin_println, builtin_read_line, builtin_read_string,
    builtin_set_print_length, builtin_setenv, builtin_slurp, builtin_spit, builtin_str,
};
use laziness::{
    builtin_delay_p, builtin_doall, builtin_dorun, builtin_lazy_seq_p, builtin_memoize,
    builtin_realized_p,
};
use logic::{builtin_boolean, builtin_not};
use math::{
    builtin_acos, builtin_asin, builtin_atan, builtin_atan2, builtin_cbrt, builtin_ceil,
    builtin_cos, builtin_cosh, builtin_e, builtin_exp, builtin_floor, builtin_hypot,
    builtin_infinite_q, builtin_log, builtin_log2, builtin_log10, builtin_nan_q, builtin_pi,
    builtin_pow, builtin_round, builtin_signum, builtin_sin, builtin_sinh, builtin_sqrt,
    builtin_tan, builtin_tanh, builtin_to_degrees, builtin_to_radians, builtin_trunc,
};
use metadata::{
    builtin_alter_meta, builtin_meta, builtin_reset_meta, builtin_vary_meta, builtin_with_meta,
};
use multimethods::{
    builtin_ancestors, builtin_descendants, builtin_get_method, builtin_isa,
    builtin_make_hierarchy, builtin_methods, builtin_parents, builtin_prefer_method,
    builtin_prefers, builtin_remove_all_methods, builtin_remove_method,
};
use predicates::{
    builtin_boolean_p, builtin_coll_p, builtin_denominator, builtin_float_p, builtin_fn_p,
    builtin_integer_p, builtin_keyword_p, builtin_list_p, builtin_map_p, builtin_nil_p,
    builtin_number_p, builtin_numerator, builtin_ratio_p, builtin_seq_p, builtin_set_p,
    builtin_some_p, builtin_string_p, builtin_symbol_p, builtin_vector_p,
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

/// Register all built-in functions in the klujur.core namespace.
pub fn register_builtins(env: &Env) {
    let registry = env.registry();
    let core_ns = registry.find_or_create(crate::namespace::NamespaceRegistry::CORE_NS);

    // Arithmetic
    core_ns.define_native("+", builtin_add);
    core_ns.define_native("-", builtin_sub);
    core_ns.define_native("*", builtin_mul);
    core_ns.define_native("/", builtin_div);
    core_ns.define_native("quot", builtin_quot);
    core_ns.define_native("rem", builtin_rem);
    core_ns.define_native("mod", builtin_mod);
    core_ns.define_native("inc", builtin_inc);
    core_ns.define_native("dec", builtin_dec);
    core_ns.define_native("max", builtin_max);
    core_ns.define_native("min", builtin_min);
    core_ns.define_native("abs", builtin_abs);
    core_ns.define_native("double", builtin_double);
    core_ns.define_native("int", builtin_int);

    // Numeric predicates
    core_ns.define_native("even?", builtin_even_p);
    core_ns.define_native("odd?", builtin_odd_p);
    core_ns.define_native("pos?", builtin_pos_p);
    core_ns.define_native("neg?", builtin_neg_p);
    core_ns.define_native("zero?", builtin_zero_p);

    // Math functions registered in klujur.math namespace
    let math_ns = registry.find_or_create("klujur.math");
    math_ns.define_native("sqrt", builtin_sqrt);
    math_ns.define_native("cbrt", builtin_cbrt);
    math_ns.define_native("pow", builtin_pow);
    math_ns.define_native("exp", builtin_exp);
    math_ns.define_native("log", builtin_log);
    math_ns.define_native("log10", builtin_log10);
    math_ns.define_native("log2", builtin_log2);
    math_ns.define_native("sin", builtin_sin);
    math_ns.define_native("cos", builtin_cos);
    math_ns.define_native("tan", builtin_tan);
    math_ns.define_native("asin", builtin_asin);
    math_ns.define_native("acos", builtin_acos);
    math_ns.define_native("atan", builtin_atan);
    math_ns.define_native("atan2", builtin_atan2);
    math_ns.define_native("sinh", builtin_sinh);
    math_ns.define_native("cosh", builtin_cosh);
    math_ns.define_native("tanh", builtin_tanh);
    math_ns.define_native("floor", builtin_floor);
    math_ns.define_native("ceil", builtin_ceil);
    math_ns.define_native("round", builtin_round);
    math_ns.define_native("trunc", builtin_trunc);
    math_ns.define_native("signum", builtin_signum);
    math_ns.define_native("hypot", builtin_hypot);
    math_ns.define_native("nan?", builtin_nan_q);
    math_ns.define_native("infinite?", builtin_infinite_q);
    math_ns.define_native("pi", builtin_pi);
    math_ns.define_native("e", builtin_e);
    math_ns.define_native("to-radians", builtin_to_radians);
    math_ns.define_native("to-degrees", builtin_to_degrees);

    // Date/time functions registered in klujur.time namespace
    let time_ns = registry.find_or_create("klujur.time");
    time_ns.define_native("system-time", builtin_system_time);
    time_ns.define_native("now-millis", builtin_now_millis);
    time_ns.define_native("now-micros", builtin_now_micros);
    time_ns.define_native("now-nanos", builtin_now_nanos);
    time_ns.define_native("now-secs", builtin_now_secs);

    // Comparison
    core_ns.define_native("=", builtin_eq);
    core_ns.define_native("<", builtin_lt);
    core_ns.define_native(">", builtin_gt);
    core_ns.define_native("<=", builtin_le);
    core_ns.define_native(">=", builtin_ge);
    core_ns.define_native("not=", builtin_not_eq);

    // Type predicates
    core_ns.define_native("nil?", builtin_nil_p);
    core_ns.define_native("some?", builtin_some_p);
    core_ns.define_native("boolean?", builtin_boolean_p);
    core_ns.define_native("number?", builtin_number_p);
    core_ns.define_native("integer?", builtin_integer_p);
    core_ns.define_native("float?", builtin_float_p);
    core_ns.define_native("ratio?", builtin_ratio_p);
    core_ns.define_native("numerator", builtin_numerator);
    core_ns.define_native("denominator", builtin_denominator);
    core_ns.define_native("string?", builtin_string_p);
    core_ns.define_native("symbol?", builtin_symbol_p);
    core_ns.define_native("keyword?", builtin_keyword_p);
    core_ns.define_native("list?", builtin_list_p);
    core_ns.define_native("vector?", builtin_vector_p);
    core_ns.define_native("map?", builtin_map_p);
    core_ns.define_native("set?", builtin_set_p);
    core_ns.define_native("fn?", builtin_fn_p);
    core_ns.define_native("coll?", builtin_coll_p);
    core_ns.define_native("seq?", builtin_seq_p);
    core_ns.define_native("var?", builtin_var_p);
    core_ns.define_native("seqable?", builtin_seqable_p);
    core_ns.define_native("sequential?", builtin_sequential_p);
    core_ns.define_native("sorted?", builtin_sorted_p);
    core_ns.define_native("counted?", builtin_counted_p);
    core_ns.define_native("reversible?", builtin_reversible_p);
    core_ns.define_native("associative?", builtin_associative_p);
    core_ns.define_native("indexed?", builtin_indexed_p);

    // Vars
    core_ns.define_native("deref", builtin_deref);

    // Atoms
    core_ns.define_native("atom", builtin_atom);
    core_ns.define_native("atom?", builtin_atom_p);
    core_ns.define_native("reset!", builtin_reset);
    // Note: swap! and swap-vals! are special forms (eval/dynamic.rs), not builtins
    core_ns.define_native("reset-vals!", builtin_reset_vals);
    core_ns.define_native("compare-and-set!", builtin_compare_and_set);
    core_ns.define_native("add-watch", builtin_add_watch);
    core_ns.define_native("remove-watch", builtin_remove_watch);
    core_ns.define_native("set-validator!", builtin_set_validator);
    core_ns.define_native("get-validator", builtin_get_validator);

    // Delays and Lazy Sequences
    core_ns.define_native("delay?", builtin_delay_p);
    // Note: force is a special form (eval/dynamic.rs), not a builtin
    core_ns.define_native("realized?", builtin_realized_p);
    core_ns.define_native("lazy-seq?", builtin_lazy_seq_p);
    core_ns.define_native("doall", builtin_doall);
    core_ns.define_native("dorun", builtin_dorun);

    // Memoization
    core_ns.define_native("memoize", builtin_memoize);

    // Sequences
    core_ns.define_native("first", builtin_first);
    core_ns.define_native("rest", builtin_rest);
    core_ns.define_native("next", builtin_next);
    core_ns.define_native("second", builtin_second);
    core_ns.define_native("last", builtin_last);
    core_ns.define_native("butlast", builtin_butlast);
    core_ns.define_native("cons", builtin_cons);
    core_ns.define_native("count", builtin_count);
    core_ns.define_native("nth", builtin_nth);
    core_ns.define_native("empty?", builtin_empty_p);
    core_ns.define_native("take*", builtin_take);
    core_ns.define_native("drop*", builtin_drop);
    core_ns.define_native("concat", builtin_concat);
    core_ns.define_native("mapcat*", builtin_mapcat);
    core_ns.define_native("partition", builtin_partition);
    core_ns.define_native("reverse", builtin_reverse);
    core_ns.define_native("range", builtin_range);
    core_ns.define_native("repeat", builtin_repeat);
    core_ns.define_native("into", builtin_into);
    core_ns.define_native("seq", builtin_seq);

    // Logic
    core_ns.define_native("not", builtin_not);
    core_ns.define_native("boolean", builtin_boolean);

    // Collections
    core_ns.define_native("list", builtin_list);
    core_ns.define_native("vector", builtin_vector);
    core_ns.define_native("get", builtin_get);
    core_ns.define_native("assoc", builtin_assoc);
    core_ns.define_native("dissoc", builtin_dissoc);
    core_ns.define_native("conj", builtin_conj);

    // I/O dynamic vars - default to keywords representing standard streams
    core_ns.intern_dynamic(
        "*in*",
        KlujurVal::Keyword(klujur_parser::Keyword::new("stdin")),
    );
    core_ns.intern_dynamic(
        "*out*",
        KlujurVal::Keyword(klujur_parser::Keyword::new("stdout")),
    );
    core_ns.intern_dynamic(
        "*err*",
        KlujurVal::Keyword(klujur_parser::Keyword::new("stderr")),
    );

    // Misc
    core_ns.define_native("str", builtin_str);
    core_ns.define_native("pr-str", builtin_pr_str);
    core_ns.define_native("print", builtin_print);
    core_ns.define_native("println", builtin_println);
    core_ns.define_native("type", builtin_type);
    core_ns.define_native("satisfies?", builtin_satisfies_p);
    core_ns.define_native("extends?", builtin_extends_p);
    core_ns.define_native("identity", builtin_identity);
    core_ns.define_native("set-print-length!", builtin_set_print_length);
    core_ns.define_native("get-print-length", builtin_get_print_length);

    // I/O functions registered in klujur.io namespace
    let io_ns = registry.find_or_create("klujur.io");
    io_ns.define_native("read-line", builtin_read_line);
    io_ns.define_native("flush", builtin_flush);
    io_ns.define_native("getenv", builtin_getenv);
    io_ns.define_native("setenv", builtin_setenv);
    io_ns.define_native("exit", builtin_exit);

    // Higher-order functions
    core_ns.define_native("apply", builtin_apply);
    core_ns.define_native("map*", builtin_map);
    core_ns.define_native("filter*", builtin_filter);
    core_ns.define_native("remove*", builtin_remove);
    core_ns.define_native("reduce", builtin_reduce);
    core_ns.define_native("comp", builtin_comp);
    core_ns.define_native("partial", builtin_partial);
    core_ns.define_native("constantly", builtin_constantly);
    core_ns.define_native("every?", builtin_every_p);
    core_ns.define_native("some", builtin_some);
    core_ns.define_native("not-any?", builtin_not_any_p);
    core_ns.define_native("not-every?", builtin_not_every_p);

    // Exceptions
    core_ns.define_native("ex-info", builtin_ex_info);
    core_ns.define_native("ex-message", builtin_ex_message);
    core_ns.define_native("ex-data", builtin_ex_data);

    // Dynamic bindings
    core_ns.define_native("bound?", builtin_bound_p);
    core_ns.define_native("thread-bound?", builtin_thread_bound_p);
    core_ns.define_native("var-get", builtin_var_get);
    core_ns.define_native("var-set", builtin_var_set);

    // String/Symbol/Keyword operations
    core_ns.define_native("name", builtin_name);
    core_ns.define_native("namespace", builtin_namespace);
    core_ns.define_native("symbol", builtin_symbol);
    core_ns.define_native("keyword", builtin_keyword);
    core_ns.define_native("subs", builtin_subs);

    // Additional predicates
    core_ns.define_native("true?", builtin_true_p);
    core_ns.define_native("false?", builtin_false_p);
    core_ns.define_native("==", builtin_num_eq);
    core_ns.define_native("compare", builtin_compare);
    core_ns.define_native("identical?", builtin_identical_p);
    core_ns.define_native("not-empty", builtin_not_empty);

    // Collection utilities
    core_ns.define_native("keys", builtin_keys);
    core_ns.define_native("vals", builtin_vals);
    core_ns.define_native("find", builtin_find);
    core_ns.define_native("contains?", builtin_contains_p);
    core_ns.define_native("select-keys", builtin_select_keys);
    core_ns.define_native("merge", builtin_merge);
    core_ns.define_native("merge-with", builtin_merge_with);
    core_ns.define_native("get-in", builtin_get_in);
    core_ns.define_native("assoc-in", builtin_assoc_in);
    core_ns.define_native("update", builtin_update);
    core_ns.define_native("update-in", builtin_update_in);
    core_ns.define_native("update-keys", builtin_update_keys);
    core_ns.define_native("update-vals", builtin_update_vals);
    core_ns.define_native("peek", builtin_peek);
    core_ns.define_native("pop", builtin_pop);
    core_ns.define_native("disj", builtin_disj);
    core_ns.define_native("empty", builtin_empty);

    // Collection constructors
    core_ns.define_native("vec", builtin_vec);
    core_ns.define_native("set", builtin_set);
    core_ns.define_native("hash-map", builtin_hash_map);
    core_ns.define_native("hash-set", builtin_hash_set);
    core_ns.define_native("sorted-map", builtin_sorted_map);
    core_ns.define_native("sorted-set", builtin_sorted_set);
    core_ns.define_native("sorted-map-by", builtin_sorted_map_by);
    core_ns.define_native("sorted-set-by", builtin_sorted_set_by);
    core_ns.define_native("list*", builtin_list_star);
    core_ns.define_native("zipmap", builtin_zipmap);

    // Bitwise operations
    core_ns.define_native("bit-and", builtin_bit_and);
    core_ns.define_native("bit-or", builtin_bit_or);
    core_ns.define_native("bit-xor", builtin_bit_xor);
    core_ns.define_native("bit-not", builtin_bit_not);
    core_ns.define_native("bit-and-not", builtin_bit_and_not);
    core_ns.define_native("bit-shift-left", builtin_bit_shift_left);
    core_ns.define_native("bit-shift-right", builtin_bit_shift_right);
    core_ns.define_native("unsigned-bit-shift-right", builtin_unsigned_bit_shift_right);
    core_ns.define_native("bit-set", builtin_bit_set);
    core_ns.define_native("bit-clear", builtin_bit_clear);
    core_ns.define_native("bit-flip", builtin_bit_flip);
    core_ns.define_native("bit-test", builtin_bit_test);

    // Additional higher-order functions
    core_ns.define_native("reduce-kv", builtin_reduce_kv);
    core_ns.define_native("juxt", builtin_juxt);
    core_ns.define_native("complement", builtin_complement);
    core_ns.define_native("fnil", builtin_fnil);
    core_ns.define_native("some-fn", builtin_some_fn);
    core_ns.define_native("every-pred", builtin_every_pred);

    // Eager sequence functions
    core_ns.define_native("sort", builtin_sort);
    core_ns.define_native("sort-by", builtin_sort_by);
    core_ns.define_native("frequencies", builtin_frequencies);
    core_ns.define_native("group-by", builtin_group_by);
    core_ns.define_native("ffirst", builtin_ffirst);
    core_ns.define_native("nfirst", builtin_nfirst);
    core_ns.define_native("nnext", builtin_nnext);
    core_ns.define_native("fnext", builtin_fnext);
    core_ns.define_native("rseq", builtin_rseq);

    // Random & utilities
    core_ns.define_native("rand", builtin_rand);
    core_ns.define_native("rand-int", builtin_rand_int);
    core_ns.define_native("rand-nth", builtin_rand_nth);
    core_ns.define_native("shuffle", builtin_shuffle);
    core_ns.define_native("gensym", builtin_gensym);
    core_ns.define_native("hash", builtin_hash);

    // Metadata
    core_ns.define_native("meta", builtin_meta);
    core_ns.define_native("with-meta", builtin_with_meta);
    core_ns.define_native("vary-meta", builtin_vary_meta);
    core_ns.define_native("alter-meta!", builtin_alter_meta);
    core_ns.define_native("reset-meta!", builtin_reset_meta);

    // I/O & evaluation
    core_ns.define_native("read-string", builtin_read_string);
    core_ns.define_native("slurp", builtin_slurp);
    core_ns.define_native("spit", builtin_spit);
    core_ns.define_native("format", builtin_format);

    // Multimethods
    core_ns.define_native("methods", builtin_methods);
    core_ns.define_native("get-method", builtin_get_method);
    core_ns.define_native("remove-method", builtin_remove_method);
    core_ns.define_native("prefer-method", builtin_prefer_method);
    core_ns.define_native("prefers", builtin_prefers);
    core_ns.define_native("remove-all-methods", builtin_remove_all_methods);

    // Hierarchies
    core_ns.define_native("make-hierarchy", builtin_make_hierarchy);
    core_ns.define_native("isa?", builtin_isa);
    core_ns.define_native("parents", builtin_parents);
    core_ns.define_native("ancestors", builtin_ancestors);
    core_ns.define_native("descendants", builtin_descendants);

    // Transducers - Reduced type
    core_ns.define_native("reduced", builtin_reduced);
    core_ns.define_native("reduced?", builtin_reduced_p);
    core_ns.define_native("unreduced", builtin_unreduced);
    core_ns.define_native("ensure-reduced", builtin_ensure_reduced);

    // Volatiles
    core_ns.define_native("volatile!", builtin_volatile);
    core_ns.define_native("volatile?", builtin_volatile_p);
    core_ns.define_native("vreset!", builtin_vreset);
    core_ns.define_native("vswap!", builtin_vswap);

    // Transducers - execution
    core_ns.define_native("transduce", builtin_transduce);

    // Refer klujur.core into the user namespace so builtins are accessible
    let user_ns = registry.find("user").expect("user namespace should exist");
    registry.refer_core_to(&user_ns);
}

use crate::namespace::Namespace;

/// Helper trait to define native functions more easily.
pub trait NsExt {
    fn define_native(&self, name: &'static str, func: fn(&[KlujurVal]) -> Result<KlujurVal>);
}

impl NsExt for Namespace {
    fn define_native(&self, name: &'static str, func: fn(&[KlujurVal]) -> Result<KlujurVal>) {
        let native = make_native_fn(name, func);
        self.intern_with_value(name, KlujurVal::NativeFn(native));
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
        // Ratio comparisons: compare a/b with c/d by comparing a*d with b*c
        (KlujurVal::Ratio(an, ad), KlujurVal::Ratio(bn, bd)) => {
            // a/b < c/d  iff  a*d < b*c (when b,d > 0, which they are after normalisation)
            let lhs = (*an as i128) * (*bd as i128);
            let rhs = (*ad as i128) * (*bn as i128);
            Ok(lhs.cmp(&rhs))
        }
        (KlujurVal::Ratio(num, den), KlujurVal::Int(y)) => {
            // num/den vs y/1: compare num with den*y
            let lhs = *num as i128;
            let rhs = (*den as i128) * (*y as i128);
            Ok(lhs.cmp(&rhs))
        }
        (KlujurVal::Int(x), KlujurVal::Ratio(num, den)) => {
            // x/1 vs num/den: compare x*den with num
            let lhs = (*x as i128) * (*den as i128);
            let rhs = *num as i128;
            Ok(lhs.cmp(&rhs))
        }
        (KlujurVal::Ratio(num, den), KlujurVal::Float(y)) => {
            let fx = *num as f64 / *den as f64;
            fx.partial_cmp(y)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))
        }
        (KlujurVal::Float(x), KlujurVal::Ratio(num, den)) => {
            let fy = *num as f64 / *den as f64;
            x.partial_cmp(&fy)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))
        }
        (a, b) => Err(Error::type_error_in(
            "comparison",
            "number",
            if !matches!(
                a,
                KlujurVal::Int(_) | KlujurVal::Float(_) | KlujurVal::Ratio(_, _)
            ) {
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

/// Helper to convert a value to a sequence of values.
///
/// # Eager Collection Limitation
///
/// This function eagerly collects all elements into a `Vec`. For lazy sequences,
/// this means the entire sequence is realised before returning. **Infinite
/// sequences will hang or cause an OOM error.**
///
/// Functions that use `to_seq` internally (e.g., `reduce`, `transduce`, `map*`,
/// `filter*`) inherit this limitation. When working with potentially infinite
/// sequences, use `take` or `take-while` to bound the sequence first:
///
/// ```clojure
/// ;; This will hang:
/// ;; (reduce + (range))
///
/// ;; Do this instead:
/// (reduce + (take 1000 (range)))
/// ```
///
/// Note: The lazy sequence functions in `core.cljc` (e.g., `map`, `filter`)
/// work correctly with infinite sequences because they produce lazy sequences.
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
