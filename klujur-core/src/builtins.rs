// klujur-core - Built-in functions
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Built-in functions for Klujur.

// Allow mutable key types - KlujurVal has interior mutability for Vars by design
#![allow(clippy::mutable_key_type)]

use klujur_parser::{
    Keyword, KlujurHierarchy, KlujurNativeFn, KlujurVal, OrdMap, Symbol, get_print_length,
    set_print_length,
};
use std::cell::RefCell;
use std::rc::Rc;

use crate::bindings::{deref_var, has_thread_binding, set_thread_binding};
use crate::env::Env;
use crate::error::{Error, Result};
use crate::eval::{apply, make_native_fn};

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
// Arithmetic
// ============================================================================

fn builtin_add(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(0));
    }

    let mut is_float = false;
    let mut int_sum: i64 = 0;
    let mut float_sum: f64 = 0.0;

    for arg in args {
        match arg {
            KlujurVal::Int(n) => {
                if is_float {
                    float_sum += *n as f64;
                } else {
                    int_sum += n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    float_sum = int_sum as f64;
                }
                float_sum += n;
            }
            other => {
                return Err(Error::type_error_in("+", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(float_sum))
    } else {
        Ok(KlujurVal::int(int_sum))
    }
}

fn builtin_sub(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // Unary negation
        return match &args[0] {
            KlujurVal::Int(n) => Ok(KlujurVal::int(-n)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(-n)),
            other => Err(Error::type_error_in("-", "number", other.type_name())),
        };
    }

    let mut is_float = false;
    let mut result: f64 = 0.0;
    let mut int_result: i64 = 0;

    for (i, arg) in args.iter().enumerate() {
        match arg {
            KlujurVal::Int(n) => {
                if i == 0 {
                    if is_float {
                        result = *n as f64;
                    } else {
                        int_result = *n;
                    }
                } else if is_float {
                    result -= *n as f64;
                } else {
                    int_result -= n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    result = int_result as f64;
                }
                if i == 0 {
                    result = *n;
                } else {
                    result -= n;
                }
            }
            other => {
                return Err(Error::type_error_in("-", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(result))
    } else {
        Ok(KlujurVal::int(int_result))
    }
}

fn builtin_mul(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Ok(KlujurVal::int(1));
    }

    let mut is_float = false;
    let mut int_prod: i64 = 1;
    let mut float_prod: f64 = 1.0;

    for arg in args {
        match arg {
            KlujurVal::Int(n) => {
                if is_float {
                    float_prod *= *n as f64;
                } else {
                    int_prod *= n;
                }
            }
            KlujurVal::Float(n) => {
                if !is_float {
                    is_float = true;
                    float_prod = int_prod as f64;
                }
                float_prod *= n;
            }
            other => {
                return Err(Error::type_error_in("*", "number", other.type_name()));
            }
        }
    }

    if is_float {
        Ok(KlujurVal::float(float_prod))
    } else {
        Ok(KlujurVal::int(int_prod))
    }
}

fn builtin_div(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // 1/x
        return match &args[0] {
            KlujurVal::Int(0) => Err(Error::DivisionByZero),
            KlujurVal::Int(n) => Ok(KlujurVal::float(1.0 / *n as f64)),
            KlujurVal::Float(n) => Ok(KlujurVal::float(1.0 / n)),
            other => Err(Error::type_error_in("/", "number", other.type_name())),
        };
    }

    let mut result = match &args[0] {
        KlujurVal::Int(n) => *n as f64,
        KlujurVal::Float(n) => *n,
        other => return Err(Error::type_error_in("/", "number", other.type_name())),
    };

    for arg in &args[1..] {
        let divisor = match arg {
            KlujurVal::Int(0) => return Err(Error::DivisionByZero),
            KlujurVal::Int(n) => *n as f64,
            KlujurVal::Float(n) => *n,
            other => return Err(Error::type_error_in("/", "number", other.type_name())),
        };
        result /= divisor;
    }

    Ok(KlujurVal::float(result))
}

fn builtin_quot(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("quot", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("quot", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("quot", "integer", other.type_name())),
    };

    Ok(KlujurVal::int(a / b))
}

fn builtin_rem(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("rem", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("rem", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("rem", "integer", other.type_name())),
    };

    Ok(KlujurVal::int(a % b))
}

fn builtin_mod(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("mod", 2, args.len()));
    }

    let a = match &args[0] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("mod", "integer", other.type_name())),
    };
    let b = match &args[1] {
        KlujurVal::Int(0) => return Err(Error::DivisionByZero),
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("mod", "integer", other.type_name())),
    };

    // Clojure's mod: result has same sign as divisor
    let rem = a % b;
    if (rem < 0 && b > 0) || (rem > 0 && b < 0) {
        Ok(KlujurVal::int(rem + b))
    } else {
        Ok(KlujurVal::int(rem))
    }
}

fn builtin_inc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("inc", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(n + 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n + 1.0)),
        other => Err(Error::type_error_in("inc", "number", other.type_name())),
    }
}

fn builtin_dec(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("dec", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(n - 1)),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n - 1.0)),
        other => Err(Error::type_error_in("dec", "number", other.type_name())),
    }
}

fn builtin_max(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let mut max = args[0].clone();
    for arg in &args[1..] {
        if compare_numbers(arg, &max)? == std::cmp::Ordering::Greater {
            max = arg.clone();
        }
    }
    Ok(max)
}

fn builtin_min(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let mut min = args[0].clone();
    for arg in &args[1..] {
        if compare_numbers(arg, &min)? == std::cmp::Ordering::Less {
            min = arg.clone();
        }
    }
    Ok(min)
}

fn builtin_abs(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("abs", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::int(n.abs())),
        KlujurVal::Float(n) => Ok(KlujurVal::float(n.abs())),
        other => Err(Error::type_error_in("abs", "number", other.type_name())),
    }
}

// ============================================================================
// Numeric Predicates
// ============================================================================

fn builtin_even_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("even?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 == 0)),
        other => Err(Error::type_error_in("even?", "integer", other.type_name())),
    }
}

fn builtin_odd_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("odd?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(n % 2 != 0)),
        other => Err(Error::type_error_in("odd?", "integer", other.type_name())),
    }
}

fn builtin_pos_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("pos?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n > 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n > 0.0)),
        other => Err(Error::type_error_in("pos?", "number", other.type_name())),
    }
}

fn builtin_neg_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("neg?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n < 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n < 0.0)),
        other => Err(Error::type_error_in("neg?", "number", other.type_name())),
    }
}

fn builtin_zero_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("zero?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Int(n) => Ok(KlujurVal::bool(*n == 0)),
        KlujurVal::Float(n) => Ok(KlujurVal::bool(*n == 0.0)),
        other => Err(Error::type_error_in("zero?", "number", other.type_name())),
    }
}

// ============================================================================
// Comparison
// ============================================================================

fn builtin_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if args[i - 1] != args[i] {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

fn builtin_not_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(false));
    }
    for i in 1..args.len() {
        if args[i - 1] == args[i] {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

fn compare_numbers(a: &KlujurVal, b: &KlujurVal) -> Result<std::cmp::Ordering> {
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

fn builtin_lt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? != std::cmp::Ordering::Less {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

fn builtin_gt(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? != std::cmp::Ordering::Greater {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

fn builtin_le(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? == std::cmp::Ordering::Greater {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

fn builtin_ge(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }
    for i in 1..args.len() {
        if compare_numbers(&args[i - 1], &args[i])? == std::cmp::Ordering::Less {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

// ============================================================================
// Type Predicates
// ============================================================================

fn builtin_nil_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nil?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Nil)))
}

fn builtin_some_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("some?", 1, args.len()));
    }
    Ok(KlujurVal::bool(!matches!(args[0], KlujurVal::Nil)))
}

fn builtin_boolean_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("boolean?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(_))))
}

fn builtin_number_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("number?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Int(_) | KlujurVal::Float(_) | KlujurVal::Ratio(_, _)
    )))
}

fn builtin_integer_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("integer?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Int(_))))
}

fn builtin_float_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("float?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Float(_))))
}

fn builtin_string_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("string?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::String(_))))
}

fn builtin_symbol_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("symbol?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Symbol(_, _))))
}

fn builtin_keyword_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("keyword?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Keyword(_))))
}

fn builtin_list_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("list?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::List(_, None))))
}

fn builtin_vector_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vector?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, None)
    )))
}

fn builtin_map_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("map?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Map(_, None))))
}

fn builtin_set_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("set?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Set(_, None))))
}

fn builtin_fn_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("fn?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Fn(_) | KlujurVal::NativeFn(_)
    )))
}

fn builtin_coll_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("coll?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
    )))
}

fn builtin_seq_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seq?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::List(_, None))))
}

// ============================================================================
// Sequences
// ============================================================================

use klujur_parser::{KlujurLazySeq, SeqResult};

/// Force a lazy sequence and return its SeqResult.
/// If already realized, returns the cached result.
fn force_lazy_seq(ls: &KlujurLazySeq) -> Result<SeqResult> {
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

fn builtin_first(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("first", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::String(s) => Ok(s
            .chars()
            .next()
            .map(KlujurVal::char)
            .unwrap_or(KlujurVal::Nil)),
        KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
            SeqResult::Empty => Ok(KlujurVal::Nil),
            SeqResult::Cons(first, _) => Ok(first),
        },
        other => Err(Error::type_error_in("first", "seqable", other.type_name())),
    }
}

fn builtin_rest(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rest", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
        }
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::empty_list())
            } else {
                Ok(KlujurVal::list(items.iter().skip(1).cloned().collect()))
            }
        }
        KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
            SeqResult::Empty => Ok(KlujurVal::empty_list()),
            SeqResult::Cons(_, rest) => Ok(rest),
        },
        other => Err(Error::type_error_in("rest", "seqable", other.type_name())),
    }
}

fn builtin_cons(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("cons", 2, args.len()));
    }

    let head = args[0].clone();
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::list(vec![head])),
        KlujurVal::List(items, _) => {
            let mut new_items = items.clone();
            new_items.push_front(head);
            Ok(KlujurVal::List(new_items, None))
        }
        KlujurVal::Vector(items, _) => {
            let mut new_items = items.clone();
            new_items.push_front(head);
            Ok(KlujurVal::List(new_items, None))
        }
        // For lazy seqs, return a Cons with the lazy seq as the rest
        // This preserves laziness - we don't force the lazy seq
        KlujurVal::LazySeq(_) => Ok(KlujurVal::LazySeq(KlujurLazySeq::from_cons(
            head,
            args[1].clone(),
        ))),
        other => Err(Error::type_error_in("cons", "seqable", other.type_name())),
    }
}

fn builtin_count(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("count", 1, args.len()));
    }

    let len = match &args[0] {
        KlujurVal::Nil => 0,
        KlujurVal::List(items, _) => items.len(),
        KlujurVal::Vector(items, _) => items.len(),
        KlujurVal::Map(map, _) => map.len(),
        KlujurVal::Set(set, _) => set.len(),
        KlujurVal::String(s) => s.chars().count(),
        KlujurVal::Record(r) => r.values.len(),
        KlujurVal::LazySeq(_) => {
            // Force the lazy-seq and count its elements
            let items = to_seq(&args[0])?;
            items.len()
        }
        other => {
            return Err(Error::type_error_in(
                "count",
                "countable",
                other.type_name(),
            ));
        }
    };

    Ok(KlujurVal::int(len as i64))
}

fn builtin_nth(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("nth".into()),
        });
    }

    let idx = match &args[1] {
        KlujurVal::Int(n) => *n,
        other => return Err(Error::type_error_in("nth", "integer", other.type_name())),
    };

    let not_found = args.get(2);

    match &args[0] {
        KlujurVal::List(items, _) => {
            if idx < 0 || idx as usize >= items.len() {
                if let Some(default) = not_found {
                    Ok(default.clone())
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: items.len(),
                    })
                }
            } else {
                Ok(items[idx as usize].clone())
            }
        }
        KlujurVal::Vector(items, _) => {
            if idx < 0 || idx as usize >= items.len() {
                if let Some(default) = not_found {
                    Ok(default.clone())
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: items.len(),
                    })
                }
            } else {
                Ok(items[idx as usize].clone())
            }
        }
        KlujurVal::String(s) => {
            if idx < 0 {
                if let Some(default) = not_found {
                    return Ok(default.clone());
                } else {
                    return Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: s.chars().count(),
                    });
                }
            }
            match s.chars().nth(idx as usize) {
                Some(c) => Ok(KlujurVal::char(c)),
                None => {
                    if let Some(default) = not_found {
                        Ok(default.clone())
                    } else {
                        Err(Error::IndexOutOfBounds {
                            index: idx,
                            length: s.chars().count(),
                        })
                    }
                }
            }
        }
        KlujurVal::LazySeq(_) => {
            // Walk through lazy seq one element at a time to support infinite seqs
            if idx < 0 {
                if let Some(default) = not_found {
                    return Ok(default.clone());
                } else {
                    return Err(Error::IndexOutOfBounds {
                        index: idx,
                        length: 0,
                    });
                }
            }
            let mut current = args[0].clone();
            for _ in 0..idx {
                match builtin_next(&[current.clone()])? {
                    KlujurVal::Nil => {
                        if let Some(default) = not_found {
                            return Ok(default.clone());
                        } else {
                            return Err(Error::IndexOutOfBounds {
                                index: idx,
                                length: 0, // Unknown length
                            });
                        }
                    }
                    next_val => current = next_val,
                }
            }
            // Get the first element of current position
            builtin_first(&[current])
        }
        other => Err(Error::type_error_in("nth", "indexed", other.type_name())),
    }
}

fn builtin_empty_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("empty?", 1, args.len()));
    }

    let is_empty = match &args[0] {
        KlujurVal::Nil => true,
        KlujurVal::List(items, _) => items.is_empty(),
        KlujurVal::Vector(items, _) => items.is_empty(),
        KlujurVal::Map(map, _) => map.is_empty(),
        KlujurVal::Set(set, _) => set.is_empty(),
        KlujurVal::String(s) => s.is_empty(),
        other => return Err(Error::type_error_in("empty?", "seqable", other.type_name())),
    };

    Ok(KlujurVal::bool(is_empty))
}

fn builtin_next(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("next", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.len() <= 1 => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().skip(1).cloned().collect())),
        KlujurVal::Vector(items, _) if items.len() <= 1 => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().skip(1).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(_, rest) => {
                    // next returns nil if rest is empty, otherwise rest as seq
                    builtin_seq(&[rest])
                }
            }
        }
        other => Err(Error::type_error_in("next", "seqable", other.type_name())),
    }
}

fn builtin_second(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("second", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.get(1).cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("second", "seqable", other.type_name())),
    }
}

fn builtin_last(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("last", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("last", "seqable", other.type_name())),
    }
}

fn builtin_butlast(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("butlast", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(
            items.iter().take(items.len() - 1).cloned().collect(),
        )),
        KlujurVal::Vector(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(
            items.iter().take(items.len() - 1).cloned().collect(),
        )),
        other => Err(Error::type_error_in(
            "butlast",
            "seqable",
            other.type_name(),
        )),
    }
}

fn builtin_take(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("take", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("take", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().take(n).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            // Take n elements from the lazy seq
            let mut result = Vec::with_capacity(n);
            let mut current = KlujurVal::LazySeq(ls.clone());
            while result.len() < n {
                match &current {
                    KlujurVal::Nil => break,
                    KlujurVal::List(items, _) if items.is_empty() => break,
                    KlujurVal::List(items, _) => {
                        let remaining = n - result.len();
                        result.extend(items.iter().take(remaining).cloned());
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
            Ok(KlujurVal::list(result))
        }
        other => Err(Error::type_error_in("take", "seqable", other.type_name())),
    }
}

fn builtin_drop(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("drop", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => return Err(Error::type_error_in("drop", "integer", other.type_name())),
    };
    match &args[1] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::list(items.iter().skip(n).cloned().collect())),
        KlujurVal::LazySeq(ls) => {
            // Drop n elements from the lazy seq, return the rest
            let mut current = KlujurVal::LazySeq(ls.clone());
            let mut dropped = 0;
            while dropped < n {
                match &current {
                    KlujurVal::Nil => return Ok(KlujurVal::empty_list()),
                    KlujurVal::List(items, _) if items.is_empty() => {
                        return Ok(KlujurVal::empty_list());
                    }
                    KlujurVal::List(items, _) => {
                        let remaining = n - dropped;
                        return Ok(KlujurVal::list(
                            items.iter().skip(remaining).cloned().collect(),
                        ));
                    }
                    KlujurVal::LazySeq(ls) => match force_lazy_seq(ls)? {
                        SeqResult::Empty => return Ok(KlujurVal::empty_list()),
                        SeqResult::Cons(_, rest) => {
                            dropped += 1;
                            current = rest;
                        }
                    },
                    _ => return Ok(KlujurVal::empty_list()),
                }
            }
            // Return the remaining sequence
            Ok(current)
        }
        other => Err(Error::type_error_in("drop", "seqable", other.type_name())),
    }
}

fn builtin_concat(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = Vec::new();
    for arg in args {
        if arg.is_nil() {
            continue;
        }
        let items = to_seq(arg)?;
        result.extend(items);
    }
    Ok(KlujurVal::list(result))
}

fn builtin_mapcat(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("mapcat", 2, args.len()));
    }
    let f = &args[0];
    let coll = to_seq(&args[1])?;

    let mut result = Vec::new();
    for item in &coll {
        let mapped = crate::apply(f, std::slice::from_ref(item))?;
        if mapped.is_nil() {
            continue;
        }
        let items = to_seq(&mapped)?;
        result.extend(items);
    }
    Ok(KlujurVal::list(result))
}

fn builtin_partition(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 4 {
        return Err(Error::EvalError(
            "partition requires 2 to 4 arguments".into(),
        ));
    }

    let n = match &args[0] {
        KlujurVal::Int(n) => *n as usize,
        other => {
            return Err(Error::type_error_in(
                "partition",
                "integer",
                other.type_name(),
            ));
        }
    };

    if n == 0 {
        return Err(Error::EvalError("partition size must be positive".into()));
    }

    let (step, coll_idx, pad) = match args.len() {
        2 => (n, 1, None),
        3 => {
            // Could be step or coll
            match &args[1] {
                KlujurVal::Int(s) => (*s as usize, 2, None),
                _ => (n, 1, None), // Treat 3rd as pad
            }
        }
        4 => {
            let step = match &args[1] {
                KlujurVal::Int(s) => *s as usize,
                other => {
                    return Err(Error::type_error_in(
                        "partition",
                        "integer",
                        other.type_name(),
                    ));
                }
            };
            let pad = Some(&args[2]);
            (step, 3, pad)
        }
        _ => unreachable!(),
    };

    let coll = to_seq(&args[coll_idx])?;
    let pad_vec = pad.map(to_seq).transpose()?.unwrap_or_default();

    let mut result = Vec::new();
    let mut i = 0;

    while i < coll.len() {
        let end = (i + n).min(coll.len());
        let chunk: Vec<KlujurVal> = coll[i..end].to_vec();

        if chunk.len() == n {
            result.push(KlujurVal::list(chunk));
        } else if pad.is_some() {
            // Pad the chunk
            let mut padded = chunk;
            let needed = n - padded.len();
            let mut pad_iter = pad_vec.iter().cycle();
            for _ in 0..needed {
                if let Some(p) = pad_iter.next() {
                    padded.push(p.clone());
                }
            }
            result.push(KlujurVal::list(padded));
        }
        // If chunk.len() < n and no pad, drop incomplete chunk

        i += step;
    }

    Ok(KlujurVal::list(result))
}

fn builtin_reverse(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("reverse", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::empty_list()),
        KlujurVal::List(items, _) => Ok(KlujurVal::list(items.iter().rev().cloned().collect())),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::vector(items.iter().rev().cloned().collect())),
        other => Err(Error::type_error_in(
            "reverse",
            "seqable",
            other.type_name(),
        )),
    }
}

fn builtin_range(args: &[KlujurVal]) -> Result<KlujurVal> {
    let (start, end, step) = match args.len() {
        0 => return Err(Error::syntax("range", "requires at least 1 argument")),
        1 => {
            let end = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (0, end, 1)
        }
        2 => {
            let start = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let end = match &args[1] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (start, end, 1)
        }
        3 => {
            let start = match &args[0] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let end = match &args[1] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            let step = match &args[2] {
                KlujurVal::Int(n) => *n,
                other => return Err(Error::type_error_in("range", "integer", other.type_name())),
            };
            (start, end, step)
        }
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(1, 3),
                got: args.len(),
                name: Some("range".into()),
            });
        }
    };

    if step == 0 {
        return Err(Error::EvalError("range step cannot be zero".into()));
    }

    let mut result = Vec::new();
    let mut i = start;
    if step > 0 {
        while i < end {
            result.push(KlujurVal::int(i));
            i += step;
        }
    } else {
        while i > end {
            result.push(KlujurVal::int(i));
            i += step;
        }
    }
    Ok(KlujurVal::list(result))
}

fn builtin_repeat(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("repeat", 2, args.len()));
    }
    let n = match &args[0] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => {
            return Err(Error::EvalError("repeat count must be non-negative".into()));
        }
        other => return Err(Error::type_error_in("repeat", "integer", other.type_name())),
    };
    let val = args[1].clone();
    Ok(KlujurVal::list(vec![val; n]))
}

fn builtin_into(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => builtin_into_2(args),
        3 => builtin_into_3(args),
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("into".into()),
        }),
    }
}

/// (into to from) - 2-arity: add all items from `from` into `to`
fn builtin_into_2(args: &[KlujurVal]) -> Result<KlujurVal> {
    let items: Vec<KlujurVal> = match &args[1] {
        KlujurVal::Nil => Vec::new(),
        KlujurVal::List(items, _) => items.iter().cloned().collect(),
        KlujurVal::Vector(items, _) => items.iter().cloned().collect(),
        other => return Err(Error::type_error_in("into", "seqable", other.type_name())),
    };

    match &args[0] {
        KlujurVal::Vector(existing, _) => {
            let mut result = existing.clone();
            for item in items {
                result.push_back(item);
            }
            Ok(KlujurVal::Vector(result, None))
        }
        KlujurVal::List(existing, _) => {
            // into prepends to list (like repeated conj)
            let mut result = existing.clone();
            for item in items {
                result.push_front(item);
            }
            Ok(KlujurVal::List(result, None))
        }
        KlujurVal::Set(existing, _) => {
            let mut result = existing.clone();
            for item in items {
                result.insert(item);
            }
            Ok(KlujurVal::Set(result, None))
        }
        KlujurVal::Map(existing, _) => {
            // Items should be pairs or vectors of [k v]
            let mut result = existing.clone();
            for item in items {
                match item {
                    KlujurVal::Vector(ref kv, _) if kv.len() == 2 => {
                        result.insert(kv[0].clone(), kv[1].clone());
                    }
                    KlujurVal::List(ref kv, _) if kv.len() == 2 => {
                        result.insert(kv[0].clone(), kv[1].clone());
                    }
                    _ => {
                        return Err(Error::type_error_in(
                            "into",
                            "key-value pair",
                            item.type_name(),
                        ));
                    }
                }
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "into",
            "collection",
            other.type_name(),
        )),
    }
}

/// (into to xform from) - 3-arity: transduce `from` through `xform` into `to`
fn builtin_into_3(args: &[KlujurVal]) -> Result<KlujurVal> {
    let to = &args[0];
    let xform = &args[1];
    let from = &args[2];

    // Get the conj function for the target collection type
    let conj_fn = KlujurVal::NativeFn(make_native_fn("conj", builtin_conj));

    // Apply transducer to conj to get transformed reducing function
    let xf = apply(xform, &[conj_fn])?;

    // Get sequence from source collection
    let items = to_seq(from)?;

    // Reduce with transformed function, starting with target collection
    let mut result = to.clone();
    for item in items {
        result = apply(&xf, &[result, item])?;
        // Check for early termination with Reduced
        if let KlujurVal::Reduced(v) = result {
            result = (*v).clone();
            break;
        }
    }

    // Call completion arity: (xf result)
    apply(&xf, &[result])
}

fn builtin_seq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seq", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::List(_, _) => Ok(args[0].clone()),
        KlujurVal::Vector(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Vector(items, _) => Ok(KlujurVal::List(items.clone(), None)),
        KlujurVal::String(s) if s.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::String(s) => Ok(KlujurVal::list(s.chars().map(KlujurVal::char).collect())),
        KlujurVal::Set(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Set(items, _) => Ok(KlujurVal::list(items.iter().cloned().collect())),
        KlujurVal::Map(items, _) if items.is_empty() => Ok(KlujurVal::Nil),
        KlujurVal::Map(items, _) => {
            let pairs: Vec<KlujurVal> = items
                .iter()
                .map(|(k, v)| KlujurVal::vector(vec![k.clone(), v.clone()]))
                .collect();
            Ok(KlujurVal::list(pairs))
        }
        KlujurVal::LazySeq(ls) => {
            // Force the lazy seq and check if empty
            match force_lazy_seq(ls)? {
                SeqResult::Empty => Ok(KlujurVal::Nil),
                SeqResult::Cons(_, _) => Ok(args[0].clone()), // Return the lazy seq itself
            }
        }
        KlujurVal::Record(r) => {
            if r.values.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                // Return seq of [key value] pairs like a map
                let pairs: Vec<KlujurVal> = r
                    .values
                    .iter()
                    .map(|(k, v)| KlujurVal::vector(vec![KlujurVal::Keyword(k.clone()), v.clone()]))
                    .collect();
                Ok(KlujurVal::list(pairs))
            }
        }
        other => Err(Error::type_error_in("seq", "seqable", other.type_name())),
    }
}

// ============================================================================
// Logic
// ============================================================================

fn builtin_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("not", 1, args.len()));
    }
    Ok(KlujurVal::bool(!args[0].is_truthy()))
}

fn builtin_boolean(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("boolean", 1, args.len()));
    }
    Ok(KlujurVal::bool(args[0].is_truthy()))
}

// ============================================================================
// Collections
// ============================================================================

fn builtin_list(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::list(args.to_vec()))
}

fn builtin_vector(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::vector(args.to_vec()))
}

fn builtin_get(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("get".into()),
        });
    }

    let not_found = args.get(2).cloned().unwrap_or(KlujurVal::Nil);

    match &args[0] {
        KlujurVal::Map(map, _) => Ok(map.get(&args[1]).cloned().unwrap_or(not_found)),
        KlujurVal::Vector(items, _) => {
            if let KlujurVal::Int(idx) = &args[1] {
                if *idx >= 0 && (*idx as usize) < items.len() {
                    Ok(items[*idx as usize].clone())
                } else {
                    Ok(not_found)
                }
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Set(set, _) => {
            if set.contains(&args[1]) {
                Ok(args[1].clone())
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Record(r) => {
            // Get on record requires keyword key
            if let KlujurVal::Keyword(kw) = &args[1] {
                Ok(r.get(kw).cloned().unwrap_or(not_found))
            } else {
                Ok(not_found)
            }
        }
        KlujurVal::Nil => Ok(not_found),
        _ => Ok(not_found),
    }
}

fn builtin_assoc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 || !(args.len() - 1).is_multiple_of(2) {
        return Err(Error::syntax("assoc", "requires coll and key-value pairs"));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let mut new_map = map.clone();
            for pair in args[1..].chunks(2) {
                new_map.insert(pair[0].clone(), pair[1].clone());
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Vector(items, _) => {
            let mut new_vec = items.clone();
            for pair in args[1..].chunks(2) {
                if let KlujurVal::Int(idx_i64) = &pair[0] {
                    let idx = *idx_i64 as usize;
                    if idx < new_vec.len() {
                        new_vec.set(idx, pair[1].clone());
                    } else {
                        return Err(Error::IndexOutOfBounds {
                            index: *idx_i64,
                            length: new_vec.len(),
                        });
                    }
                } else {
                    return Err(Error::type_error_in(
                        "assoc",
                        "integer",
                        pair[0].type_name(),
                    ));
                }
            }
            Ok(KlujurVal::Vector(new_vec, None))
        }
        KlujurVal::Record(r) => {
            // assoc on record preserves record type
            let mut new_record = (**r).clone();
            for pair in args[1..].chunks(2) {
                if let KlujurVal::Keyword(kw) = &pair[0] {
                    new_record.values.insert(kw.clone(), pair[1].clone());
                } else {
                    return Err(Error::type_error_in(
                        "assoc",
                        "keyword",
                        pair[0].type_name(),
                    ));
                }
            }
            Ok(KlujurVal::Record(std::rc::Rc::new(new_record)))
        }
        KlujurVal::Nil => {
            let mut new_map = klujur_parser::OrdMap::new();
            for pair in args[1..].chunks(2) {
                new_map.insert(pair[0].clone(), pair[1].clone());
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        other => Err(Error::type_error_in(
            "assoc",
            "associative",
            other.type_name(),
        )),
    }
}

fn builtin_dissoc(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let mut new_map = map.clone();
            for key in &args[1..] {
                new_map.remove(key);
            }
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Record(r) => {
            // dissoc on record: if base field removed -> returns Map, else Record
            let mut result = KlujurVal::Record(r.clone());
            for key in &args[1..] {
                if let KlujurVal::Keyword(kw) = key {
                    // RecordInstance::dissoc returns appropriate type
                    if let KlujurVal::Record(curr_r) = &result {
                        result = curr_r.dissoc(kw);
                    } else if let KlujurVal::Map(m, _) = &result {
                        // Already converted to map, continue as map
                        let mut new_map = m.clone();
                        new_map.remove(key);
                        result = KlujurVal::Map(new_map, None);
                    }
                }
            }
            Ok(result)
        }
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        other => Err(Error::type_error_in("dissoc", "map", other.type_name())),
    }
}

fn builtin_conj(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    match &args[0] {
        KlujurVal::List(items, _) => {
            // conj adds to front of list
            let mut result = items.clone();
            for item in args[1..].iter().rev() {
                result.push_front(item.clone());
            }
            Ok(KlujurVal::List(result, None))
        }
        KlujurVal::Vector(items, _) => {
            // conj adds to end of vector
            let mut result = items.clone();
            for item in &args[1..] {
                result.push_back(item.clone());
            }
            Ok(KlujurVal::Vector(result, None))
        }
        KlujurVal::Set(set, _) => {
            let mut new_set = set.clone();
            for item in &args[1..] {
                new_set.insert(item.clone());
            }
            Ok(KlujurVal::Set(new_set, None))
        }
        KlujurVal::Nil => Ok(KlujurVal::list(args[1..].to_vec())),
        other => Err(Error::type_error_in(
            "conj",
            "collection",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Misc
// ============================================================================

fn builtin_str(args: &[KlujurVal]) -> Result<KlujurVal> {
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

fn builtin_pr_str(args: &[KlujurVal]) -> Result<KlujurVal> {
    let parts: Vec<String> = args.iter().map(|a| format!("{}", a)).collect();
    Ok(KlujurVal::string(parts.join(" ")))
}

fn builtin_print(args: &[KlujurVal]) -> Result<KlujurVal> {
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

fn builtin_println(args: &[KlujurVal]) -> Result<KlujurVal> {
    builtin_print(args)?;
    println!();
    Ok(KlujurVal::Nil)
}

fn builtin_type(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("type", 1, args.len()));
    }
    // For records, return the record type name as a symbol
    if let KlujurVal::Record(r) = &args[0] {
        Ok(KlujurVal::Symbol(r.record_type.clone(), None))
    } else {
        Ok(KlujurVal::string(args[0].type_name()))
    }
}

/// (satisfies? protocol value) - Check if value's type implements the protocol
fn builtin_satisfies_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("satisfies?", 2, args.len()));
    }

    let protocol = match &args[0] {
        KlujurVal::Protocol(p) => p.protocol(),
        other => {
            return Err(Error::type_error("protocol", other.type_name()));
        }
    };

    let value = &args[1];
    let type_key = value.type_key();

    Ok(KlujurVal::Bool(protocol.has_impl(&type_key)))
}

/// (extends? protocol type-symbol) - Check if a type extends the protocol
/// Note: type-symbol should be one of: String, Vector, List, Map, etc.
fn builtin_extends_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    use klujur_parser::TypeKey;

    if args.len() != 2 {
        return Err(Error::arity_named("extends?", 2, args.len()));
    }

    let protocol = match &args[0] {
        KlujurVal::Protocol(p) => p.protocol(),
        other => {
            return Err(Error::type_error("protocol", other.type_name()));
        }
    };

    // Convert the type symbol to a TypeKey
    let type_key = match &args[1] {
        KlujurVal::Symbol(sym, _) => match sym.name() {
            "nil" => TypeKey::Nil,
            "Boolean" | "Bool" => TypeKey::Bool,
            "Integer" | "Long" | "Int" => TypeKey::Int,
            "Float" | "Double" => TypeKey::Float,
            "Ratio" => TypeKey::Ratio,
            "Char" | "Character" => TypeKey::Char,
            "String" => TypeKey::String,
            "Symbol" => TypeKey::Symbol,
            "Keyword" => TypeKey::Keyword,
            "List" | "PersistentList" => TypeKey::List,
            "Vector" | "PersistentVector" => TypeKey::Vector,
            "Map" | "HashMap" | "PersistentHashMap" => TypeKey::Map,
            "Set" | "HashSet" | "PersistentHashSet" => TypeKey::Set,
            "Fn" | "Function" | "IFn" => TypeKey::Fn,
            "Var" => TypeKey::Var,
            "Atom" => TypeKey::Atom,
            "Delay" => TypeKey::Delay,
            "LazySeq" => TypeKey::LazySeq,
            "Multimethod" => TypeKey::Multimethod,
            "Hierarchy" => TypeKey::Hierarchy,
            "Reduced" => TypeKey::Reduced,
            "Volatile" => TypeKey::Volatile,
            name => TypeKey::Record(klujur_parser::Symbol::new(name)),
        },
        other => {
            return Err(Error::type_error("symbol", other.type_name()));
        }
    };

    Ok(KlujurVal::Bool(protocol.has_impl(&type_key)))
}

fn builtin_identity(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("identity", 1, args.len()));
    }
    Ok(args[0].clone())
}

/// (set-print-length! n) - set the maximum number of elements to print in sequences
/// n can be nil (unlimited) or a positive integer
fn builtin_set_print_length(args: &[KlujurVal]) -> Result<KlujurVal> {
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
fn builtin_get_print_length(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("get-print-length", 0, args.len()));
    }
    Ok(get_print_length()
        .map(|n| KlujurVal::int(n as i64))
        .unwrap_or(KlujurVal::Nil))
}

// ============================================================================
// Higher-Order Functions
// ============================================================================

/// (apply f args) or (apply f a b c args) - apply function to arguments
fn builtin_apply(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let func = &args[0];

    // Collect all arguments: intermediate args + spread of final seq
    let mut all_args = Vec::new();

    // Add intermediate arguments (everything except first and last)
    for arg in &args[1..args.len() - 1] {
        all_args.push(arg.clone());
    }

    // Spread the last argument (must be a seqable)
    let last = &args[args.len() - 1];
    match last {
        KlujurVal::List(items, _) => all_args.extend(items.iter().cloned()),
        KlujurVal::Vector(items, _) => all_args.extend(items.iter().cloned()),
        KlujurVal::Nil => {} // nil as empty seq
        KlujurVal::LazySeq(_) => {
            // Force the lazy seq and spread its elements
            let items = to_seq(last)?;
            all_args.extend(items);
        }
        other => {
            return Err(Error::type_error_in("apply", "seqable", other.type_name()));
        }
    }

    // Call the function with the collected arguments
    apply(func, &all_args)
}

/// Helper to convert a value to a sequence of values
fn to_seq(val: &KlujurVal) -> Result<Vec<KlujurVal>> {
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

/// (map f coll) - apply f to each element, return lazy seq
fn builtin_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let func = &args[0];

    if args.len() == 2 {
        // Single collection
        let items = to_seq(&args[1])?;
        let mut result = Vec::with_capacity(items.len());
        for item in items {
            result.push(apply(func, &[item])?);
        }
        Ok(KlujurVal::list(result))
    } else {
        // Multiple collections - zip them
        let colls: Result<Vec<Vec<KlujurVal>>> = args[1..].iter().map(to_seq).collect();
        let colls = colls?;

        // Find minimum length
        let min_len = colls.iter().map(|c| c.len()).min().unwrap_or(0);

        let mut result = Vec::with_capacity(min_len);
        for i in 0..min_len {
            let call_args: Vec<KlujurVal> = colls.iter().map(|c| c[i].clone()).collect();
            result.push(apply(func, &call_args)?);
        }
        Ok(KlujurVal::list(result))
    }
}

/// (filter pred coll) - return elements where (pred elem) is truthy
fn builtin_filter(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("filter", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    let mut result = Vec::new();
    for item in items {
        let test = apply(pred, std::slice::from_ref(&item))?;
        if test.is_truthy() {
            result.push(item);
        }
    }
    Ok(KlujurVal::list(result))
}

/// (remove pred coll) - return elements where (pred elem) is falsy
fn builtin_remove(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    let mut result = Vec::new();
    for item in items {
        let test = apply(pred, std::slice::from_ref(&item))?;
        if !test.is_truthy() {
            result.push(item);
        }
    }
    Ok(KlujurVal::list(result))
}

/// (reduce f init coll) or (reduce f coll) - reduce collection
fn builtin_reduce(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("reduce".into()),
        });
    }

    let func = &args[0];

    if args.len() == 2 {
        // No initial value - use first element
        let items = to_seq(&args[1])?;
        if items.is_empty() {
            // (reduce f []) => (f)
            return apply(func, &[]);
        }
        let mut acc = items[0].clone();
        for item in &items[1..] {
            acc = apply(func, &[acc, item.clone()])?;
            // Check for early termination with Reduced
            if let KlujurVal::Reduced(v) = acc {
                return Ok((*v).clone());
            }
        }
        Ok(acc)
    } else {
        // With initial value
        let items = to_seq(&args[2])?;
        let mut acc = args[1].clone();
        for item in items {
            acc = apply(func, &[acc, item])?;
            // Check for early termination with Reduced
            if let KlujurVal::Reduced(v) = acc {
                return Ok((*v).clone());
            }
        }
        Ok(acc)
    }
}

/// (comp f g ...) - compose functions right-to-left
fn builtin_comp(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.is_empty() {
        // (comp) returns identity
        return Ok(KlujurVal::NativeFn(crate::eval::make_native_fn(
            "comp",
            builtin_identity,
        )));
    }

    // Store functions in reverse order for right-to-left composition
    let funcs: Vec<KlujurVal> = args.iter().rev().cloned().collect();
    let funcs_rc = Rc::new(funcs);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut result = apply(&funcs_rc[0], call_args)?;
        for f in funcs_rc.iter().skip(1) {
            result = apply(f, &[result])?;
        }
        Ok(result)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "comp", func_any,
    )))
}

/// (partial f arg1 arg2 ...) - partially apply function
fn builtin_partial(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let func = args[0].clone();
    let bound_args: Vec<KlujurVal> = args[1..].to_vec();

    let func_rc = Rc::new(func);
    let bound_rc = Rc::new(bound_args);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut all_args = (*bound_rc).clone();
        all_args.extend(call_args.iter().cloned());
        apply(&func_rc, &all_args)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "partial", func_any,
    )))
}

/// (constantly x) - return a function that always returns x
fn builtin_constantly(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.len() != 1 {
        return Err(Error::arity_named("constantly", 1, args.len()));
    }

    let value = args[0].clone();
    let value_rc = Rc::new(value);

    let closure = move |_call_args: &[KlujurVal]| -> Result<KlujurVal> { Ok((*value_rc).clone()) };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "constantly",
        func_any,
    )))
}

/// (every? pred coll) - true if (pred x) is truthy for all x
fn builtin_every_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("every?", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    for item in items {
        let test = apply(pred, &[item])?;
        if !test.is_truthy() {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (some pred coll) - return first truthy result of (pred x), or nil
fn builtin_some(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("some", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    for item in items {
        let test = apply(pred, &[item])?;
        if test.is_truthy() {
            return Ok(test);
        }
    }
    Ok(KlujurVal::Nil)
}

/// (not-any? pred coll) - true if (pred x) is falsy for all x
fn builtin_not_any_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("not-any?", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    for item in items {
        let test = apply(pred, &[item])?;
        if test.is_truthy() {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (not-every? pred coll) - true if (pred x) is falsy for any x
fn builtin_not_every_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("not-every?", 2, args.len()));
    }

    let pred = &args[0];
    let items = to_seq(&args[1])?;

    for item in items {
        let test = apply(pred, &[item])?;
        if !test.is_truthy() {
            return Ok(KlujurVal::bool(true));
        }
    }
    Ok(KlujurVal::bool(false))
}

// ============================================================================
// Vars
// ============================================================================

/// (var? x) - true if x is a Var
fn builtin_var_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("var?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(&args[0], KlujurVal::Var(_))))
}

/// (deref var) - get the value of a Var (also works with @var syntax when implemented)
fn builtin_deref(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("deref", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(v.deref()),
        KlujurVal::Atom(a) => Ok(a.deref()),
        KlujurVal::Delay(d) => {
            // If already realized, return cached value
            if let Some(val) = d.get_cached() {
                Ok(val)
            } else {
                // Deref on unrealized delay requires special form handling
                Err(Error::syntax(
                    "deref",
                    "deref on unrealized delay must be called directly (use @delay or force)",
                ))
            }
        }
        KlujurVal::Volatile(v) => Ok(v.deref()),
        other => Err(Error::type_error(
            "Var, Atom, Delay, or Volatile",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Atoms
// ============================================================================

/// (atom x) - Create an atom with initial value x
fn builtin_atom(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("atom", 1, args.len()));
    }
    Ok(KlujurVal::atom(args[0].clone()))
}

/// (atom? x) - Returns true if x is an atom
fn builtin_atom_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("atom?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Atom(_))))
}

/// (reset! atom newval) - Set atom value, returns newval
fn builtin_reset(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset!", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            // TODO: Run validator if present
            a.set_value(args[1].clone());
            Ok(args[1].clone())
        }
        other => Err(Error::type_error_in("reset!", "atom", other.type_name())),
    }
}

/// (swap! atom f & args) - Apply f to current value (and optional args)
/// This is a placeholder - swap! is implemented as a special form in eval.rs
fn builtin_swap(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    // This should never be called - swap! is handled as a special form
    Err(Error::syntax(
        "swap!",
        "swap! must be called directly, not passed as a value",
    ))
}

/// (swap-vals! atom f & args) - Like swap!, returns [old new]
/// This is a placeholder - swap-vals! is implemented as a special form in eval.rs
fn builtin_swap_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    // This should never be called - swap-vals! is handled as a special form
    Err(Error::syntax(
        "swap-vals!",
        "swap-vals! must be called directly, not passed as a value",
    ))
}

/// (reset-vals! atom newval) - Set atom value, returns [old new]
fn builtin_reset_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset-vals!", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            let (old, new) = a.reset_vals(args[1].clone());
            Ok(KlujurVal::vector(vec![old, new]))
        }
        other => Err(Error::type_error_in(
            "reset-vals!",
            "atom",
            other.type_name(),
        )),
    }
}

/// (compare-and-set! atom oldval newval) - CAS, returns true if successful
fn builtin_compare_and_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("compare-and-set!", 3, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            let success = a.compare_and_set(&args[1], args[2].clone());
            Ok(KlujurVal::bool(success))
        }
        other => Err(Error::type_error_in(
            "compare-and-set!",
            "atom",
            other.type_name(),
        )),
    }
}

/// (add-watch atom key fn) - Add a watch function
fn builtin_add_watch(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("add-watch", 3, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            a.add_watch(args[1].clone(), args[2].clone());
            Ok(args[0].clone())
        }
        other => Err(Error::type_error_in("add-watch", "atom", other.type_name())),
    }
}

/// (remove-watch atom key) - Remove a watch function
fn builtin_remove_watch(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove-watch", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            a.remove_watch(&args[1]);
            Ok(args[0].clone())
        }
        other => Err(Error::type_error_in(
            "remove-watch",
            "atom",
            other.type_name(),
        )),
    }
}

/// (set-validator! atom fn) - Set validation function (nil to remove)
fn builtin_set_validator(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("set-validator!", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => {
            let validator = match &args[1] {
                KlujurVal::Nil => None,
                f => Some(f.clone()),
            };
            a.set_validator(validator);
            Ok(KlujurVal::Nil)
        }
        other => Err(Error::type_error_in(
            "set-validator!",
            "atom",
            other.type_name(),
        )),
    }
}

/// (get-validator atom) - Get validation function or nil
fn builtin_get_validator(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("get-validator", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Atom(a) => Ok(a.get_validator().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "get-validator",
            "atom",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Delays
// ============================================================================

/// (delay? x) - Returns true if x is a delay
fn builtin_delay_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("delay?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Delay(_))))
}

/// (realized? x) - Returns true if a lazy value has been realized
fn builtin_realized_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("realized?", 1, args.len()));
    }
    let realized = match &args[0] {
        KlujurVal::Delay(d) => d.is_realized(),
        KlujurVal::LazySeq(ls) => ls.is_realized(),
        // Non-lazy values are always "realized"
        _ => true,
    };
    Ok(KlujurVal::bool(realized))
}

/// (lazy-seq? x) - Returns true if x is a lazy sequence
fn builtin_lazy_seq_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("lazy-seq?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::LazySeq(_))))
}

/// (doall coll) - Force the entire lazy sequence and return it
fn builtin_doall(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("doall", 1, args.len()));
    }

    let coll = args[0].clone();
    let mut current = coll.clone();

    // Walk through the sequence, forcing each element
    loop {
        match current {
            KlujurVal::Nil => break,
            KlujurVal::List(ref items, _) if items.is_empty() => break,
            KlujurVal::List(ref items, _) => {
                if items.len() <= 1 {
                    break;
                }
                current = KlujurVal::list(items.iter().skip(1).cloned().collect());
            }
            KlujurVal::LazySeq(ref ls) => match force_lazy_seq(ls)? {
                SeqResult::Empty => break,
                SeqResult::Cons(_, rest) => {
                    current = rest;
                }
            },
            _ => break,
        }
    }

    Ok(coll)
}

/// (dorun coll) - Force the entire lazy sequence, return nil (for side effects)
fn builtin_dorun(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("dorun", 1, args.len()));
    }

    // Reuse doall logic but return nil
    builtin_doall(args)?;
    Ok(KlujurVal::Nil)
}

/// (force x) - Force evaluation of delay (or return x if not a delay)
fn builtin_force(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("force", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Delay(d) => {
            // If already realized, return cached value
            if let Some(val) = d.get_cached() {
                return Ok(val);
            }
            // This should never be called directly - force needs to be a special form
            // to evaluate the thunk. This builtin is here for error message.
            Err(Error::syntax(
                "force",
                "force must be called directly to evaluate delays",
            ))
        }
        // Non-delay values are returned unchanged
        other => Ok(other.clone()),
    }
}

// ============================================================================
// Memoization
// ============================================================================

use std::collections::HashMap;

/// A memoized wrapper around a function
struct MemoizedFn {
    /// The original function
    f: KlujurVal,
    /// Cache: args -> result
    cache: RefCell<HashMap<Vec<KlujurVal>, KlujurVal>>,
}

impl MemoizedFn {
    fn new(f: KlujurVal) -> Self {
        MemoizedFn {
            f,
            cache: RefCell::new(HashMap::new()),
        }
    }

    fn call(&self, args: &[KlujurVal]) -> Result<KlujurVal> {
        let key: Vec<KlujurVal> = args.to_vec();

        // Check cache first
        if let Some(cached) = self.cache.borrow().get(&key) {
            return Ok(cached.clone());
        }

        // Call the original function
        let result = crate::eval::apply(&self.f, args)?;

        // Cache the result
        self.cache.borrow_mut().insert(key, result.clone());

        Ok(result)
    }
}

/// (memoize f) - Returns a cached version of f
fn builtin_memoize(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;

    if args.len() != 1 {
        return Err(Error::arity_named("memoize", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Fn(_) | KlujurVal::NativeFn(_) => {
            // Create the memoized wrapper
            let memo = Rc::new(MemoizedFn::new(args[0].clone()));

            // Create a native function that calls the memoized wrapper
            let closure =
                move |call_args: &[KlujurVal]| -> Result<KlujurVal> { memo.call(call_args) };

            // Double Rc wrapping required for native functions
            let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
            let func_any: Rc<dyn Any> = Rc::new(func_rc);
            Ok(KlujurVal::NativeFn(KlujurNativeFn::new(
                "memoized-fn",
                func_any,
            )))
        }
        other => Err(Error::type_error_in(
            "memoize",
            "function",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Exceptions
// ============================================================================

/// (ex-info msg data) - create an exception info map
/// Returns {:message msg :data data}
fn builtin_ex_info(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("ex-info", 2, args.len()));
    }

    let message = match &args[0] {
        KlujurVal::String(s) => KlujurVal::String(s.clone()),
        other => {
            return Err(Error::type_error_in("ex-info", "string", other.type_name()));
        }
    };

    let data = &args[1];
    if !matches!(data, KlujurVal::Map(_, None)) {
        return Err(Error::type_error_in("ex-info", "map", data.type_name()));
    }

    Ok(KlujurVal::map(vec![
        (
            KlujurVal::Keyword(klujur_parser::Keyword::new("message")),
            message,
        ),
        (
            KlujurVal::Keyword(klujur_parser::Keyword::new("data")),
            data.clone(),
        ),
    ]))
}

/// (ex-message ex) - get the message from an exception
fn builtin_ex_message(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ex-message", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let message_key = KlujurVal::Keyword(klujur_parser::Keyword::new("message"));
            Ok(map.get(&message_key).cloned().unwrap_or(KlujurVal::Nil))
        }
        KlujurVal::String(s) => Ok(KlujurVal::String(s.clone())),
        _ => Ok(KlujurVal::Nil),
    }
}

/// (ex-data ex) - get the data map from an exception
fn builtin_ex_data(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ex-data", 1, args.len()));
    }

    match &args[0] {
        KlujurVal::Map(map, _) => {
            let data_key = KlujurVal::Keyword(klujur_parser::Keyword::new("data"));
            Ok(map.get(&data_key).cloned().unwrap_or(KlujurVal::Nil))
        }
        _ => Ok(KlujurVal::Nil),
    }
}

// ============================================================================
// Dynamic Bindings
// ============================================================================

/// (bound? var) - check if a var has a value (root or thread-local)
fn builtin_bound_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("bound?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(_) => {
            // In our implementation, all vars have a root value when created
            Ok(KlujurVal::bool(true))
        }
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (thread-bound? var) - check if a var has a thread-local binding
fn builtin_thread_bound_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("thread-bound?", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(KlujurVal::bool(has_thread_binding(v))),
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (var-get var) - get the value of a var (checking thread-local bindings)
fn builtin_var_get(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("var-get", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => Ok(deref_var(v)),
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

/// (var-set var val) - set the value of a var in thread-local context
fn builtin_var_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("var-set", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Var(v) => {
            if !v.is_dynamic() {
                return Err(Error::EvalError(format!(
                    "can't set non-dynamic var: {}",
                    v.qualified_name()
                )));
            }
            let val = args[1].clone();
            if set_thread_binding(v, val.clone()) {
                Ok(val)
            } else {
                Err(Error::EvalError(format!(
                    "can't set {} outside of binding context",
                    v.qualified_name()
                )))
            }
        }
        other => Err(Error::type_error("Var", other.type_name())),
    }
}

// ============================================================================
// String/Symbol/Keyword Operations
// ============================================================================

/// (name x) - returns name part of keyword/symbol/string
fn builtin_name(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("name", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Keyword(kw) => Ok(KlujurVal::string(kw.name())),
        KlujurVal::Symbol(sym, _) => Ok(KlujurVal::string(sym.name())),
        KlujurVal::String(s) => Ok(KlujurVal::String(s.clone())),
        other => Err(Error::type_error_in(
            "name",
            "keyword, symbol, or string",
            other.type_name(),
        )),
    }
}

/// (namespace x) - returns namespace part of keyword/symbol, or nil
fn builtin_namespace(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("namespace", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Keyword(kw) => Ok(kw
            .namespace()
            .map(KlujurVal::string)
            .unwrap_or(KlujurVal::Nil)),
        KlujurVal::Symbol(sym, _) => Ok(sym
            .namespace()
            .map(KlujurVal::string)
            .unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "namespace",
            "keyword or symbol",
            other.type_name(),
        )),
    }
}

/// (symbol name) or (symbol ns name) - create symbol
fn builtin_symbol(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => match &args[0] {
            KlujurVal::String(s) => Ok(KlujurVal::Symbol(Symbol::parse(s), None)),
            KlujurVal::Symbol(sym, _) => Ok(KlujurVal::Symbol(sym.clone(), None)),
            other => Err(Error::type_error_in("symbol", "string", other.type_name())),
        },
        2 => {
            let ns = match &args[0] {
                KlujurVal::Nil => None,
                KlujurVal::String(s) => Some(s.as_ref()),
                other => {
                    return Err(Error::type_error_in(
                        "symbol",
                        "string or nil",
                        other.type_name(),
                    ));
                }
            };
            let name = match &args[1] {
                KlujurVal::String(s) => s.as_ref(),
                other => return Err(Error::type_error_in("symbol", "string", other.type_name())),
            };
            Ok(KlujurVal::Symbol(
                match ns {
                    Some(ns) => Symbol::with_namespace(ns, name),
                    None => Symbol::new(name),
                },
                None,
            ))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("symbol".into()),
        }),
    }
}

/// (keyword name) or (keyword ns name) - create keyword
fn builtin_keyword(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => match &args[0] {
            KlujurVal::String(s) => Ok(KlujurVal::Keyword(Keyword::parse(s))),
            KlujurVal::Keyword(kw) => Ok(KlujurVal::Keyword(kw.clone())),
            KlujurVal::Symbol(sym, _) => {
                let kw = match sym.namespace() {
                    Some(ns) => Keyword::with_namespace(ns, sym.name()),
                    None => Keyword::new(sym.name()),
                };
                Ok(KlujurVal::Keyword(kw))
            }
            other => Err(Error::type_error_in(
                "keyword",
                "string, symbol, or keyword",
                other.type_name(),
            )),
        },
        2 => {
            let ns = match &args[0] {
                KlujurVal::Nil => None,
                KlujurVal::String(s) => Some(s.as_ref()),
                other => {
                    return Err(Error::type_error_in(
                        "keyword",
                        "string or nil",
                        other.type_name(),
                    ));
                }
            };
            let name = match &args[1] {
                KlujurVal::String(s) => s.as_ref(),
                other => return Err(Error::type_error_in("keyword", "string", other.type_name())),
            };
            Ok(KlujurVal::Keyword(match ns {
                Some(ns) => Keyword::with_namespace(ns, name),
                None => Keyword::new(name),
            }))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("keyword".into()),
        }),
    }
}

/// (subs s start) or (subs s start end) - substring
fn builtin_subs(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("subs".into()),
        });
    }

    let s = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("subs", "string", other.type_name())),
    };

    let start = match &args[1] {
        KlujurVal::Int(n) if *n >= 0 => *n as usize,
        KlujurVal::Int(_) => {
            return Err(Error::EvalError(
                "subs: start index must be non-negative".into(),
            ));
        }
        other => return Err(Error::type_error_in("subs", "integer", other.type_name())),
    };

    // Convert string to chars for proper Unicode handling
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();

    if start > len {
        return Err(Error::IndexOutOfBounds {
            index: start as i64,
            length: len,
        });
    }

    let end = if args.len() == 3 {
        match &args[2] {
            KlujurVal::Int(n) if *n >= 0 => (*n as usize).min(len),
            KlujurVal::Int(_) => {
                return Err(Error::EvalError(
                    "subs: end index must be non-negative".into(),
                ));
            }
            other => return Err(Error::type_error_in("subs", "integer", other.type_name())),
        }
    } else {
        len
    };

    if end < start {
        return Err(Error::EvalError(format!(
            "subs: end index {} is less than start index {}",
            end, start
        )));
    }

    let result: String = chars[start..end].iter().collect();
    Ok(KlujurVal::string(result))
}

// ============================================================================
// Additional Predicates
// ============================================================================

/// (true? x) - exactly true (not just truthy)
fn builtin_true_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("true?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(true))))
}

/// (false? x) - exactly false (not just falsy)
fn builtin_false_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("false?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(args[0], KlujurVal::Bool(false))))
}

/// (== x y & more) - numeric equality (coerces types)
fn builtin_num_eq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Ok(KlujurVal::bool(true));
    }

    // Convert first arg to f64 for comparison
    let first = match &args[0] {
        KlujurVal::Int(n) => *n as f64,
        KlujurVal::Float(n) => *n,
        other => return Err(Error::type_error_in("==", "number", other.type_name())),
    };

    for arg in &args[1..] {
        let val = match arg {
            KlujurVal::Int(n) => *n as f64,
            KlujurVal::Float(n) => *n,
            other => return Err(Error::type_error_in("==", "number", other.type_name())),
        };
        if first != val {
            return Ok(KlujurVal::bool(false));
        }
    }
    Ok(KlujurVal::bool(true))
}

/// (compare x y) - returns -1, 0, or 1
fn builtin_compare(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("compare", 2, args.len()));
    }

    let ord = match (&args[0], &args[1]) {
        // Numbers
        (KlujurVal::Int(a), KlujurVal::Int(b)) => a.cmp(b),
        (KlujurVal::Float(a), KlujurVal::Float(b)) => a
            .partial_cmp(b)
            .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?,
        (KlujurVal::Int(a), KlujurVal::Float(b)) => {
            let fa = *a as f64;
            fa.partial_cmp(b)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?
        }
        (KlujurVal::Float(a), KlujurVal::Int(b)) => {
            let fb = *b as f64;
            a.partial_cmp(&fb)
                .ok_or_else(|| Error::EvalError("Cannot compare NaN".into()))?
        }
        // Strings
        (KlujurVal::String(a), KlujurVal::String(b)) => a.cmp(b),
        // Keywords
        (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a.cmp(b),
        // Symbols
        (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a.cmp(b),
        // Vectors (lexicographic)
        (KlujurVal::Vector(a, _), KlujurVal::Vector(b, None)) => {
            for (x, y) in a.iter().zip(b.iter()) {
                let cmp = builtin_compare(&[x.clone(), y.clone()])?;
                if let KlujurVal::Int(n) = cmp
                    && n != 0
                {
                    return Ok(cmp);
                }
            }
            a.len().cmp(&b.len())
        }
        // Booleans (false < true)
        (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a.cmp(b),
        // Nil
        (KlujurVal::Nil, KlujurVal::Nil) => std::cmp::Ordering::Equal,
        // Type mismatch
        (a, b) => {
            return Err(Error::EvalError(format!(
                "compare: cannot compare {} and {}",
                a.type_name(),
                b.type_name()
            )));
        }
    };

    Ok(KlujurVal::int(match ord {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }))
}

/// (identical? x y) - reference equality
fn builtin_identical_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("identical?", 2, args.len()));
    }

    // For value types, check value equality
    // For reference types, check pointer equality
    let identical = match (&args[0], &args[1]) {
        (KlujurVal::Nil, KlujurVal::Nil) => true,
        (KlujurVal::Bool(a), KlujurVal::Bool(b)) => a == b,
        (KlujurVal::Int(a), KlujurVal::Int(b)) => a == b,
        (KlujurVal::Float(a), KlujurVal::Float(b)) => a.to_bits() == b.to_bits(),
        (KlujurVal::Char(a), KlujurVal::Char(b)) => a == b,
        // For Rc types, we use pointer equality
        (KlujurVal::String(a), KlujurVal::String(b)) => std::ptr::eq(a.as_ref(), b.as_ref()),
        (KlujurVal::Symbol(a, _), KlujurVal::Symbol(b, _)) => a == b, // Interned, pointer eq
        (KlujurVal::Keyword(a), KlujurVal::Keyword(b)) => a == b,     // Interned, pointer eq
        // Different types are never identical
        _ => false,
    };

    Ok(KlujurVal::bool(identical))
}

/// (not-empty coll) - returns coll if non-empty, else nil
fn builtin_not_empty(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("not-empty", 1, args.len()));
    }

    let is_empty = match &args[0] {
        KlujurVal::Nil => true,
        KlujurVal::List(items, _) => items.is_empty(),
        KlujurVal::Vector(items, _) => items.is_empty(),
        KlujurVal::Map(map, _) => map.is_empty(),
        KlujurVal::Set(set, _) => set.is_empty(),
        KlujurVal::String(s) => s.is_empty(),
        other => {
            return Err(Error::type_error_in(
                "not-empty",
                "seqable",
                other.type_name(),
            ));
        }
    };

    if is_empty {
        Ok(KlujurVal::Nil)
    } else {
        Ok(args[0].clone())
    }
}

/// (seqable? x) - can call seq on x?
fn builtin_seqable_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("seqable?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Nil
            | KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::String(_)
    )))
}

/// (sequential? x) - is x sequential (list/vector)?
fn builtin_sequential_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sequential?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _) | KlujurVal::Vector(_, _)
    )))
}

/// (sorted? x) - is x a sorted collection?
fn builtin_sorted_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("sorted?", 1, args.len()));
    }
    // Our OrdMap and OrdSet are sorted by default
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Map(_, _) | KlujurVal::Set(_, _)
    )))
}

/// (counted? x) - is count O(1)?
fn builtin_counted_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("counted?", 1, args.len()));
    }
    // All our collections have O(1) count
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::List(_, _)
            | KlujurVal::Vector(_, _)
            | KlujurVal::Map(_, _)
            | KlujurVal::Set(_, _)
            | KlujurVal::String(_)
    )))
}

/// (reversible? x) - can call rseq on x?
fn builtin_reversible_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("reversible?", 1, args.len()));
    }
    // Vectors and sorted collections are reversible
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, _) | KlujurVal::Map(_, _) | KlujurVal::Set(_, _)
    )))
}

/// (associative? x) - supports assoc? (map/vector)
fn builtin_associative_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("associative?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Map(_, _) | KlujurVal::Vector(_, _)
    )))
}

/// (indexed? x) - supports nth?
fn builtin_indexed_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("indexed?", 1, args.len()));
    }
    Ok(KlujurVal::bool(matches!(
        args[0],
        KlujurVal::Vector(_, _) | KlujurVal::List(_, _) | KlujurVal::String(_)
    )))
}

// ============================================================================
// Collection Utilities
// ============================================================================

/// (keys map) - returns sequence of map keys
fn builtin_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("keys", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(KlujurVal::list(map.keys().cloned().collect())),
        KlujurVal::Record(r) => {
            // Return keywords for all fields in the record
            let keys: Vec<KlujurVal> = r
                .values
                .keys()
                .map(|k| KlujurVal::Keyword(k.clone()))
                .collect();
            Ok(KlujurVal::list(keys))
        }
        other => Err(Error::type_error_in("keys", "map", other.type_name())),
    }
}

/// (vals map) - returns sequence of map values
fn builtin_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vals", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(KlujurVal::list(map.values().cloned().collect())),
        KlujurVal::Record(r) => {
            // Return values for all fields in the record
            let vals: Vec<KlujurVal> = r.values.values().cloned().collect();
            Ok(KlujurVal::list(vals))
        }
        other => Err(Error::type_error_in("vals", "map", other.type_name())),
    }
}

/// (find map key) - returns map entry [key value] for key, or nil
fn builtin_find(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("find", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => Ok(map
            .get(&args[1])
            .map(|v| KlujurVal::vector(vec![args[1].clone(), v.clone()]))
            .unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in("find", "map", other.type_name())),
    }
}

/// (contains? coll key) - true if key present (index for vectors)
fn builtin_contains_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("contains?", 2, args.len()));
    }
    let contains = match &args[0] {
        KlujurVal::Nil => false,
        KlujurVal::Map(map, _) => map.contains_key(&args[1]),
        KlujurVal::Set(set, _) => set.contains(&args[1]),
        KlujurVal::Vector(items, _) => {
            // For vectors, contains? checks index not value
            match &args[1] {
                KlujurVal::Int(idx) => *idx >= 0 && (*idx as usize) < items.len(),
                _ => false,
            }
        }
        other => {
            return Err(Error::type_error_in(
                "contains?",
                "associative collection",
                other.type_name(),
            ));
        }
    };
    Ok(KlujurVal::bool(contains))
}

/// (select-keys map keyseq) - returns map with only specified keys
fn builtin_select_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("select-keys", 2, args.len()));
    }
    let map = match &args[0] {
        KlujurVal::Nil => return Ok(KlujurVal::map(vec![])),
        KlujurVal::Map(m, _) => m,
        other => {
            return Err(Error::type_error_in(
                "select-keys",
                "map",
                other.type_name(),
            ));
        }
    };
    let keys = to_seq(&args[1])?;
    let mut result = klujur_parser::OrdMap::new();
    for key in keys {
        if let Some(val) = map.get(&key) {
            result.insert(key, val.clone());
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (merge & maps) - merge maps left-to-right
fn builtin_merge(args: &[KlujurVal]) -> Result<KlujurVal> {
    let mut result = klujur_parser::OrdMap::new();
    for arg in args {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    result.insert(k.clone(), v.clone());
                }
            }
            other => return Err(Error::type_error_in("merge", "map", other.type_name())),
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (merge-with f & maps) - merge maps, applying f to duplicate keys
fn builtin_merge_with(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    let func = &args[0];
    let mut result: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for arg in &args[1..] {
        match arg {
            KlujurVal::Nil => {}
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    if let Some(existing) = result.get(k) {
                        let merged = apply(func, &[existing.clone(), v.clone()])?;
                        result.insert(k.clone(), merged);
                    } else {
                        result.insert(k.clone(), v.clone());
                    }
                }
            }
            other => return Err(Error::type_error_in("merge-with", "map", other.type_name())),
        }
    }
    Ok(KlujurVal::Map(result, None))
}

/// (get-in m ks) or (get-in m ks not-found) - get nested value via key path
fn builtin_get_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 || args.len() > 3 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("get-in".into()),
        });
    }
    let not_found = args.get(2).cloned().unwrap_or(KlujurVal::Nil);
    let keys = to_seq(&args[1])?;

    let mut current = args[0].clone();
    for key in keys {
        current = match &current {
            KlujurVal::Map(map, _) => map.get(&key).cloned().unwrap_or_else(|| not_found.clone()),
            KlujurVal::Vector(items, _) => {
                if let KlujurVal::Int(idx) = &key {
                    if *idx >= 0 && (*idx as usize) < items.len() {
                        items[*idx as usize].clone()
                    } else {
                        return Ok(not_found);
                    }
                } else {
                    return Ok(not_found);
                }
            }
            KlujurVal::Nil => return Ok(not_found),
            _ => return Ok(not_found),
        };
    }
    Ok(current)
}

/// (assoc-in m ks v) - associate nested value via key path
fn builtin_assoc_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("assoc-in", 3, args.len()));
    }
    let keys = to_seq(&args[1])?;
    if keys.is_empty() {
        return Ok(args[2].clone());
    }

    fn assoc_in_helper(m: &KlujurVal, keys: &[KlujurVal], v: &KlujurVal) -> Result<KlujurVal> {
        if keys.is_empty() {
            return Ok(v.clone());
        }
        let k = &keys[0];
        if keys.len() == 1 {
            // Base case: assoc the value
            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), v.clone());
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, v.clone());
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("assoc-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => {
                    // Create new map
                    Ok(KlujurVal::map(vec![(k.clone(), v.clone())]))
                }
                other => Err(Error::type_error_in(
                    "assoc-in",
                    "associative",
                    other.type_name(),
                )),
            }
        } else {
            // Recursive case: get nested value and recurse
            let nested = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                other => {
                    return Err(Error::type_error_in(
                        "assoc-in",
                        "associative",
                        other.type_name(),
                    ));
                }
            };
            let new_nested = assoc_in_helper(&nested, &keys[1..], v)?;
            // Now assoc the new nested value
            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_nested);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_nested);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("assoc-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_nested)])),
                other => Err(Error::type_error_in(
                    "assoc-in",
                    "associative",
                    other.type_name(),
                )),
            }
        }
    }

    assoc_in_helper(&args[0], &keys, &args[2])
}

/// (update m k f & args) - update value at key by applying f
fn builtin_update(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 {
        return Err(Error::arity_at_least(3, args.len()));
    }
    let m = &args[0];
    let k = &args[1];
    let f = &args[2];
    let extra_args = &args[3..];

    match m {
        KlujurVal::Map(map, _) => {
            let current = map.get(k).cloned().unwrap_or(KlujurVal::Nil);
            let mut call_args = vec![current];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;
            let mut new_map = map.clone();
            new_map.insert(k.clone(), new_val);
            Ok(KlujurVal::Map(new_map, None))
        }
        KlujurVal::Vector(items, _) => {
            if let KlujurVal::Int(idx) = k {
                if *idx >= 0 && (*idx as usize) < items.len() {
                    let current = items[*idx as usize].clone();
                    let mut call_args = vec![current];
                    call_args.extend(extra_args.iter().cloned());
                    let new_val = apply(f, &call_args)?;
                    let mut new_vec = items.clone();
                    new_vec.set(*idx as usize, new_val);
                    Ok(KlujurVal::Vector(new_vec, None))
                } else {
                    Err(Error::IndexOutOfBounds {
                        index: *idx,
                        length: items.len(),
                    })
                }
            } else {
                Err(Error::type_error_in("update", "integer", k.type_name()))
            }
        }
        KlujurVal::Nil => {
            // Treat nil as empty map
            let mut call_args = vec![KlujurVal::Nil];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;
            Ok(KlujurVal::map(vec![(k.clone(), new_val)]))
        }
        other => Err(Error::type_error_in(
            "update",
            "associative",
            other.type_name(),
        )),
    }
}

/// (update-in m ks f & args) - update nested value by applying f
fn builtin_update_in(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 3 {
        return Err(Error::arity_at_least(3, args.len()));
    }
    let m = &args[0];
    let keys = to_seq(&args[1])?;
    let f = &args[2];
    let extra_args = &args[3..];

    if keys.is_empty() {
        // Apply f directly to m
        let mut call_args = vec![m.clone()];
        call_args.extend(extra_args.iter().cloned());
        return apply(f, &call_args);
    }

    fn update_in_helper(
        m: &KlujurVal,
        keys: &[KlujurVal],
        f: &KlujurVal,
        extra_args: &[KlujurVal],
    ) -> Result<KlujurVal> {
        if keys.is_empty() {
            let mut call_args = vec![m.clone()];
            call_args.extend(extra_args.iter().cloned());
            return apply(f, &call_args);
        }

        let k = &keys[0];
        if keys.len() == 1 {
            // Base case: apply f to the value at key
            builtin_update(&[
                m.clone(),
                k.clone(),
                f.clone(),
                // Pack extra_args into rest
            ])?;
            // Actually need to call with extra args
            let current = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                _ => KlujurVal::Nil,
            };
            let mut call_args = vec![current];
            call_args.extend(extra_args.iter().cloned());
            let new_val = apply(f, &call_args)?;

            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_val);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_val);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("update-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_val)])),
                other => Err(Error::type_error_in(
                    "update-in",
                    "associative",
                    other.type_name(),
                )),
            }
        } else {
            // Recursive case
            let nested = match m {
                KlujurVal::Map(map, _) => map.get(k).cloned().unwrap_or(KlujurVal::Nil),
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        if *idx >= 0 && (*idx as usize) < items.len() {
                            items[*idx as usize].clone()
                        } else {
                            KlujurVal::Nil
                        }
                    } else {
                        KlujurVal::Nil
                    }
                }
                KlujurVal::Nil => KlujurVal::Nil,
                other => {
                    return Err(Error::type_error_in(
                        "update-in",
                        "associative",
                        other.type_name(),
                    ));
                }
            };
            let new_nested = update_in_helper(&nested, &keys[1..], f, extra_args)?;

            match m {
                KlujurVal::Map(map, _) => {
                    let mut new_map = map.clone();
                    new_map.insert(k.clone(), new_nested);
                    Ok(KlujurVal::Map(new_map, None))
                }
                KlujurVal::Vector(items, _) => {
                    if let KlujurVal::Int(idx) = k {
                        let mut new_vec = items.clone();
                        if *idx >= 0 && (*idx as usize) < new_vec.len() {
                            new_vec.set(*idx as usize, new_nested);
                            Ok(KlujurVal::Vector(new_vec, None))
                        } else {
                            Err(Error::IndexOutOfBounds {
                                index: *idx,
                                length: items.len(),
                            })
                        }
                    } else {
                        Err(Error::type_error_in("update-in", "integer", k.type_name()))
                    }
                }
                KlujurVal::Nil => Ok(KlujurVal::map(vec![(k.clone(), new_nested)])),
                other => Err(Error::type_error_in(
                    "update-in",
                    "associative",
                    other.type_name(),
                )),
            }
        }
    }

    update_in_helper(m, &keys, f, extra_args)
}

/// (update-keys m f) - apply f to all keys in map
fn builtin_update_keys(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("update-keys", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => {
            let f = &args[1];
            let mut result = klujur_parser::OrdMap::new();
            for (k, v) in map.iter() {
                let new_k = apply(f, std::slice::from_ref(k))?;
                result.insert(new_k, v.clone());
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "update-keys",
            "map",
            other.type_name(),
        )),
    }
}

/// (update-vals m f) - apply f to all values in map
fn builtin_update_vals(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("update-vals", 2, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Map(map, _) => {
            let f = &args[1];
            let mut result = klujur_parser::OrdMap::new();
            for (k, v) in map.iter() {
                let new_v = apply(f, std::slice::from_ref(v))?;
                result.insert(k.clone(), new_v);
            }
            Ok(KlujurVal::Map(result, None))
        }
        other => Err(Error::type_error_in(
            "update-vals",
            "map",
            other.type_name(),
        )),
    }
}

/// (peek coll) - get head without removing (last for vector, first for list)
fn builtin_peek(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("peek", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(items, _) => Ok(items.front().cloned().unwrap_or(KlujurVal::Nil)),
        KlujurVal::Vector(items, _) => Ok(items.back().cloned().unwrap_or(KlujurVal::Nil)),
        other => Err(Error::type_error_in(
            "peek",
            "list or vector",
            other.type_name(),
        )),
    }
}

/// (pop coll) - remove head element (last for vector, first for list)
fn builtin_pop(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("pop", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::List(items, _) => {
            if items.is_empty() {
                Err(Error::EvalError("can't pop empty list".into()))
            } else {
                let mut new_items = items.clone();
                new_items.pop_front();
                Ok(KlujurVal::List(new_items, None))
            }
        }
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Err(Error::EvalError("can't pop empty vector".into()))
            } else {
                let mut new_items = items.clone();
                new_items.pop_back();
                Ok(KlujurVal::Vector(new_items, None))
            }
        }
        other => Err(Error::type_error_in(
            "pop",
            "list or vector",
            other.type_name(),
        )),
    }
}

/// (disj set & keys) - remove keys from set
fn builtin_disj(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::Set(set, _) => {
            let mut new_set = set.clone();
            for key in &args[1..] {
                new_set.remove(key);
            }
            Ok(KlujurVal::Set(new_set, None))
        }
        other => Err(Error::type_error_in("disj", "set", other.type_name())),
    }
}

/// (empty coll) - returns empty collection of same type
fn builtin_empty(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("empty", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        KlujurVal::List(_, _) => Ok(KlujurVal::empty_list()),
        KlujurVal::Vector(_, _) => Ok(KlujurVal::vector(vec![])),
        KlujurVal::Map(_, _) => Ok(KlujurVal::map(vec![])),
        KlujurVal::Set(_, _) => Ok(KlujurVal::set(vec![])),
        KlujurVal::String(_) => Ok(KlujurVal::string("")),
        other => Err(Error::type_error_in(
            "empty",
            "collection",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Collection Constructors
// ============================================================================

/// (vec coll) - convert collection to vector
fn builtin_vec(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("vec", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::vector(vec![])),
        KlujurVal::Vector(_, _) => Ok(args[0].clone()),
        _ => {
            let items = to_seq(&args[0])?;
            Ok(KlujurVal::vector(items))
        }
    }
}

/// (set coll) - convert collection to set
fn builtin_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("set", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Nil => Ok(KlujurVal::set(vec![])),
        KlujurVal::Set(_, _) => Ok(args[0].clone()),
        _ => {
            let items = to_seq(&args[0])?;
            Ok(KlujurVal::set(items))
        }
    }
}

/// (hash-map & kvs) - create hash map from key-value pairs
fn builtin_hash_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.len().is_multiple_of(2) {
        return Err(Error::syntax(
            "hash-map",
            "requires an even number of arguments",
        ));
    }
    let mut result = klujur_parser::OrdMap::new();
    for pair in args.chunks(2) {
        result.insert(pair[0].clone(), pair[1].clone());
    }
    Ok(KlujurVal::Map(result, None))
}

/// (hash-set & keys) - create hash set from elements
fn builtin_hash_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    Ok(KlujurVal::set(args.to_vec()))
}

/// (sorted-map & kvs) - create sorted map (our default map is already sorted)
fn builtin_sorted_map(args: &[KlujurVal]) -> Result<KlujurVal> {
    // Our OrdMap is already sorted
    builtin_hash_map(args)
}

/// (sorted-set & keys) - create sorted set (our default set is already sorted)
fn builtin_sorted_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    // Our OrdSet is already sorted
    builtin_hash_set(args)
}

/// (list* args) or (list* a args) or (list* a b args) - create list with last arg spread
fn builtin_list_star(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    if args.len() == 1 {
        // (list* coll) => seq of coll
        return builtin_seq(args);
    }

    // Collect all but last arg, then spread the last
    let mut result: Vec<KlujurVal> = args[..args.len() - 1].to_vec();
    let last = &args[args.len() - 1];
    let spread = to_seq(last)?;
    result.extend(spread);

    Ok(KlujurVal::list(result))
}

/// (zipmap keys vals) - create map from parallel key/value seqs
fn builtin_zipmap(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("zipmap", 2, args.len()));
    }
    let keys = to_seq(&args[0])?;
    let vals = to_seq(&args[1])?;

    let mut result = klujur_parser::OrdMap::new();
    for (k, v) in keys.into_iter().zip(vals) {
        result.insert(k, v);
    }
    Ok(KlujurVal::Map(result, None))
}

// ============================================================================
// Bitwise Operations
// ============================================================================

/// Helper to get integer for bitwise ops
fn require_int(name: &str, val: &KlujurVal) -> Result<i64> {
    match val {
        KlujurVal::Int(n) => Ok(*n),
        other => Err(Error::type_error_in(name, "integer", other.type_name())),
    }
}

/// (bit-and x y & more) - bitwise AND
fn builtin_bit_and(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-and", &args[0])?;
    for arg in &args[1..] {
        result &= require_int("bit-and", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-or x y & more) - bitwise OR
fn builtin_bit_or(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-or", &args[0])?;
    for arg in &args[1..] {
        result |= require_int("bit-or", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-xor x y & more) - bitwise XOR
fn builtin_bit_xor(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-xor", &args[0])?;
    for arg in &args[1..] {
        result ^= require_int("bit-xor", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-not x) - bitwise complement
fn builtin_bit_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("bit-not", 1, args.len()));
    }
    let x = require_int("bit-not", &args[0])?;
    Ok(KlujurVal::int(!x))
}

/// (bit-and-not x y & more) - bitwise AND with complement
fn builtin_bit_and_not(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }
    let mut result = require_int("bit-and-not", &args[0])?;
    for arg in &args[1..] {
        result &= !require_int("bit-and-not", arg)?;
    }
    Ok(KlujurVal::int(result))
}

/// (bit-shift-left x n) - shift left
fn builtin_bit_shift_left(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-shift-left", 2, args.len()));
    }
    let x = require_int("bit-shift-left", &args[0])?;
    let n = require_int("bit-shift-left", &args[1])? as u32;
    Ok(KlujurVal::int(x << n))
}

/// (bit-shift-right x n) - arithmetic shift right
fn builtin_bit_shift_right(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-shift-right", 2, args.len()));
    }
    let x = require_int("bit-shift-right", &args[0])?;
    let n = require_int("bit-shift-right", &args[1])? as u32;
    Ok(KlujurVal::int(x >> n))
}

/// (unsigned-bit-shift-right x n) - logical shift right
fn builtin_unsigned_bit_shift_right(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named(
            "unsigned-bit-shift-right",
            2,
            args.len(),
        ));
    }
    let x = require_int("unsigned-bit-shift-right", &args[0])? as u64;
    let n = require_int("unsigned-bit-shift-right", &args[1])? as u32;
    Ok(KlujurVal::int((x >> n) as i64))
}

/// (bit-set x n) - set bit n
fn builtin_bit_set(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-set", 2, args.len()));
    }
    let x = require_int("bit-set", &args[0])?;
    let n = require_int("bit-set", &args[1])? as u32;
    Ok(KlujurVal::int(x | (1 << n)))
}

/// (bit-clear x n) - clear bit n
fn builtin_bit_clear(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-clear", 2, args.len()));
    }
    let x = require_int("bit-clear", &args[0])?;
    let n = require_int("bit-clear", &args[1])? as u32;
    Ok(KlujurVal::int(x & !(1 << n)))
}

/// (bit-flip x n) - flip bit n
fn builtin_bit_flip(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-flip", 2, args.len()));
    }
    let x = require_int("bit-flip", &args[0])?;
    let n = require_int("bit-flip", &args[1])? as u32;
    Ok(KlujurVal::int(x ^ (1 << n)))
}

/// (bit-test x n) - test bit n
fn builtin_bit_test(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("bit-test", 2, args.len()));
    }
    let x = require_int("bit-test", &args[0])?;
    let n = require_int("bit-test", &args[1])? as u32;
    Ok(KlujurVal::bool((x >> n) & 1 == 1))
}

// ============================================================================
// Additional Higher-Order Functions
// ============================================================================

/// (reduce-kv f init coll) - reduce with key-value pairs
fn builtin_reduce_kv(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("reduce-kv", 3, args.len()));
    }
    let f = &args[0];
    let mut acc = args[1].clone();

    match &args[2] {
        KlujurVal::Map(map, _) => {
            for (k, v) in map.iter() {
                acc = apply(f, &[acc, k.clone(), v.clone()])?;
            }
            Ok(acc)
        }
        KlujurVal::Vector(items, _) => {
            for (i, v) in items.iter().enumerate() {
                acc = apply(f, &[acc, KlujurVal::int(i as i64), v.clone()])?;
            }
            Ok(acc)
        }
        KlujurVal::Nil => Ok(acc),
        other => Err(Error::type_error_in(
            "reduce-kv",
            "map or vector",
            other.type_name(),
        )),
    }
}

/// (juxt f & fs) - returns fn applying each f, returning vector
fn builtin_juxt(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let funcs: Vec<KlujurVal> = args.to_vec();
    let funcs_rc = Rc::new(funcs);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut results = Vec::with_capacity(funcs_rc.len());
        for f in funcs_rc.iter() {
            results.push(apply(f, call_args)?);
        }
        Ok(KlujurVal::vector(results))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "juxt", func_any,
    )))
}

/// (complement f) - returns fn returning logical opposite
fn builtin_complement(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.len() != 1 {
        return Err(Error::arity_named("complement", 1, args.len()));
    }

    let f = args[0].clone();
    let f_rc = Rc::new(f);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let result = apply(&f_rc, call_args)?;
        Ok(KlujurVal::bool(!result.is_truthy()))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "complement",
        func_any,
    )))
}

/// (fnil f default & defaults) - wrap f to replace nil args with defaults
fn builtin_fnil(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.len() < 2 {
        return Err(Error::arity_at_least(2, args.len()));
    }

    let f = args[0].clone();
    let defaults: Vec<KlujurVal> = args[1..].to_vec();

    let f_rc = Rc::new(f);
    let defaults_rc = Rc::new(defaults);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        let mut new_args: Vec<KlujurVal> = call_args.to_vec();
        for (i, default) in defaults_rc.iter().enumerate() {
            if i < new_args.len() && matches!(new_args[i], KlujurVal::Nil) {
                new_args[i] = default.clone();
            }
        }
        apply(&f_rc, &new_args)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "fnil", func_any,
    )))
}

/// (some-fn p & ps) - returns fn returning first truthy predicate result
fn builtin_some_fn(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let preds: Vec<KlujurVal> = args.to_vec();
    let preds_rc = Rc::new(preds);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        for arg in call_args {
            for pred in preds_rc.iter() {
                let result = apply(pred, std::slice::from_ref(arg))?;
                if result.is_truthy() {
                    return Ok(result);
                }
            }
        }
        Ok(KlujurVal::Nil)
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "some-fn", func_any,
    )))
}

/// (every-pred p & ps) - returns fn returning true if all predicates true
fn builtin_every_pred(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::any::Any;
    use std::rc::Rc;

    if args.is_empty() {
        return Err(Error::arity_at_least(1, 0));
    }

    let preds: Vec<KlujurVal> = args.to_vec();
    let preds_rc = Rc::new(preds);

    let closure = move |call_args: &[KlujurVal]| -> Result<KlujurVal> {
        for arg in call_args {
            for pred in preds_rc.iter() {
                let result = apply(pred, std::slice::from_ref(arg))?;
                if !result.is_truthy() {
                    return Ok(KlujurVal::bool(false));
                }
            }
        }
        Ok(KlujurVal::bool(true))
    };

    let func_rc: Rc<crate::eval::NativeFnImpl> = Rc::new(closure);
    let func_any: Rc<dyn Any> = Rc::new(func_rc);
    Ok(KlujurVal::NativeFn(klujur_parser::KlujurNativeFn::new(
        "every-pred",
        func_any,
    )))
}

// ============================================================================
// Eager Sequence Functions
// ============================================================================

/// (sort coll) or (sort comp coll) - sort collection
fn builtin_sort(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            let mut items = to_seq(&args[0])?;
            items.sort_by(|a, b| {
                // Use compare for sorting
                match builtin_compare(&[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    _ => std::cmp::Ordering::Equal,
                }
            });
            Ok(KlujurVal::list(items))
        }
        2 => {
            let comp = &args[0];
            let mut items = to_seq(&args[1])?;
            // Use comparator function
            items.sort_by(|a, b| match apply(comp, &[a.clone(), b.clone()]) {
                Ok(KlujurVal::Int(n)) => {
                    if n < 0 {
                        std::cmp::Ordering::Less
                    } else if n > 0 {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                }
                Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Less,
                Ok(KlujurVal::Bool(false)) => std::cmp::Ordering::Greater,
                _ => std::cmp::Ordering::Equal,
            });
            Ok(KlujurVal::list(items))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(1, 2),
            got: args.len(),
            name: Some("sort".into()),
        }),
    }
}

/// (sort-by keyfn coll) or (sort-by keyfn comp coll) - sort by key function
fn builtin_sort_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            let keyfn = &args[0];
            let items = to_seq(&args[1])?;
            // Pre-compute keys
            let mut keyed: Vec<(KlujurVal, KlujurVal)> = items
                .into_iter()
                .map(|item| {
                    let key = apply(keyfn, std::slice::from_ref(&item)).unwrap_or(KlujurVal::Nil);
                    (key, item)
                })
                .collect();
            keyed.sort_by(
                |(a, _), (b, _)| match builtin_compare(&[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    _ => std::cmp::Ordering::Equal,
                },
            );
            let items: Vec<_> = keyed.into_iter().map(|(_, v)| v).collect();
            Ok(KlujurVal::list(items))
        }
        3 => {
            let keyfn = &args[0];
            let comp = &args[1];
            let items = to_seq(&args[2])?;
            // Pre-compute keys
            let mut keyed: Vec<(KlujurVal, KlujurVal)> = items
                .into_iter()
                .map(|item| {
                    let key = apply(keyfn, std::slice::from_ref(&item)).unwrap_or(KlujurVal::Nil);
                    (key, item)
                })
                .collect();
            keyed.sort_by(
                |(a, _), (b, _)| match apply(comp, &[a.clone(), b.clone()]) {
                    Ok(KlujurVal::Int(n)) => {
                        if n < 0 {
                            std::cmp::Ordering::Less
                        } else if n > 0 {
                            std::cmp::Ordering::Greater
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    }
                    Ok(KlujurVal::Bool(true)) => std::cmp::Ordering::Less,
                    Ok(KlujurVal::Bool(false)) => std::cmp::Ordering::Greater,
                    _ => std::cmp::Ordering::Equal,
                },
            );
            let items: Vec<_> = keyed.into_iter().map(|(_, v)| v).collect();
            Ok(KlujurVal::list(items))
        }
        _ => Err(Error::ArityError {
            expected: crate::error::AritySpec::Range(2, 3),
            got: args.len(),
            name: Some("sort-by".into()),
        }),
    }
}

/// (frequencies coll) - map of element->count
fn builtin_frequencies(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("frequencies", 1, args.len()));
    }
    let items = to_seq(&args[0])?;
    let mut counts: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for item in items {
        let count = counts
            .get(&item)
            .and_then(|v| {
                if let KlujurVal::Int(n) = v {
                    Some(*n)
                } else {
                    None
                }
            })
            .unwrap_or(0);
        counts.insert(item, KlujurVal::int(count + 1));
    }
    Ok(KlujurVal::Map(counts, None))
}

/// (group-by f coll) - map of (f elem)->elements
fn builtin_group_by(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("group-by", 2, args.len()));
    }
    let f = &args[0];
    let items = to_seq(&args[1])?;

    let mut groups: klujur_parser::OrdMap<KlujurVal, KlujurVal> = klujur_parser::OrdMap::new();
    for item in items {
        let key = apply(f, std::slice::from_ref(&item))?;
        let existing = groups
            .get(&key)
            .cloned()
            .unwrap_or_else(|| KlujurVal::vector(vec![]));
        let new_vec = match existing {
            KlujurVal::Vector(mut v, _) => {
                v.push_back(item);
                KlujurVal::Vector(v, None)
            }
            _ => KlujurVal::vector(vec![item]),
        };
        groups.insert(key, new_vec);
    }
    Ok(KlujurVal::Map(groups, None))
}

/// (ffirst x) - (first (first x))
fn builtin_ffirst(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("ffirst", 1, args.len()));
    }
    let first = builtin_first(args)?;
    builtin_first(&[first])
}

/// (nfirst x) - (next (first x))
fn builtin_nfirst(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nfirst", 1, args.len()));
    }
    let first = builtin_first(args)?;
    builtin_next(&[first])
}

/// (nnext x) - (next (next x))
fn builtin_nnext(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("nnext", 1, args.len()));
    }
    let next1 = builtin_next(args)?;
    builtin_next(&[next1])
}

/// (fnext x) - (first (next x))
fn builtin_fnext(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("fnext", 1, args.len()));
    }
    let next1 = builtin_next(args)?;
    builtin_first(&[next1])
}

/// (rseq coll) - reverse seq (O(1) for vectors)
fn builtin_rseq(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rseq", 1, args.len()));
    }
    match &args[0] {
        KlujurVal::Vector(items, _) => {
            if items.is_empty() {
                Ok(KlujurVal::Nil)
            } else {
                Ok(KlujurVal::list(items.iter().rev().cloned().collect()))
            }
        }
        KlujurVal::Nil => Ok(KlujurVal::Nil),
        other => Err(Error::type_error_in(
            "rseq",
            "reversible collection",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Random & Utilities
// ============================================================================

use std::sync::atomic::{AtomicU64, Ordering};

/// Global counter for gensym
static GENSYM_COUNTER: AtomicU64 = AtomicU64::new(0);

/// (rand) or (rand n) - random float 0-1 or 0-n
fn builtin_rand(args: &[KlujurVal]) -> Result<KlujurVal> {
    use std::time::{SystemTime, UNIX_EPOCH};

    // Simple random using time-based seed (not cryptographically secure)
    let seed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;
    let random = ((seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407)) as f64)
        / (u64::MAX as f64);

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
fn builtin_rand_int(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rand-int", 1, args.len()));
    }
    let n = require_int("rand-int", &args[0])?;
    if n <= 0 {
        return Err(Error::EvalError("rand-int: n must be positive".into()));
    }

    use std::time::{SystemTime, UNIX_EPOCH};
    let seed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;
    let random = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    Ok(KlujurVal::int((random % (n as u64)) as i64))
}

/// (rand-nth coll) - random element from collection
fn builtin_rand_nth(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("rand-nth", 1, args.len()));
    }
    let items = to_seq(&args[0])?;
    if items.is_empty() {
        return Err(Error::EvalError("rand-nth: collection is empty".into()));
    }

    use std::time::{SystemTime, UNIX_EPOCH};
    let seed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;
    let random = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let idx = (random % (items.len() as u64)) as usize;
    Ok(items[idx].clone())
}

/// (shuffle coll) - return shuffled collection
fn builtin_shuffle(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("shuffle", 1, args.len()));
    }
    let mut items = to_seq(&args[0])?;

    use std::time::{SystemTime, UNIX_EPOCH};
    let mut seed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;

    // Fisher-Yates shuffle
    for i in (1..items.len()).rev() {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let j = (seed % ((i + 1) as u64)) as usize;
        items.swap(i, j);
    }

    Ok(KlujurVal::vector(items))
}

/// (gensym) or (gensym prefix) - generate unique symbol
fn builtin_gensym(args: &[KlujurVal]) -> Result<KlujurVal> {
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

/// (hash x) - hash code for value
fn builtin_hash(args: &[KlujurVal]) -> Result<KlujurVal> {
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
        KlujurVal::Volatile(v) => std::ptr::hash(v.value_cell(), hasher),
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
    }
}

// ============================================================================
// I/O & Evaluation
// ============================================================================

/// (read-string s) - parse string to form
fn builtin_read_string(args: &[KlujurVal]) -> Result<KlujurVal> {
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
fn builtin_slurp(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("slurp", 1, args.len()));
    }
    let path = match &args[0] {
        KlujurVal::String(s) => s.as_ref(),
        other => return Err(Error::type_error_in("slurp", "string", other.type_name())),
    };

    std::fs::read_to_string(path)
        .map(KlujurVal::string)
        .map_err(|e| Error::EvalError(format!("slurp: {}", e)))
}

/// (spit filename content) or (spit filename content opts) - write to file
fn builtin_spit(args: &[KlujurVal]) -> Result<KlujurVal> {
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
            .map_err(|e| Error::EvalError(format!("spit: {}", e)))?;
        file.write_all(content.as_bytes())
            .map_err(|e| Error::EvalError(format!("spit: {}", e)))?;
    } else {
        std::fs::write(path, content).map_err(|e| Error::EvalError(format!("spit: {}", e)))?;
    }

    Ok(KlujurVal::Nil)
}

/// (format fmt & args) - Printf-style string formatting
/// Supports: %s (string), %d (integer), %f (float), %% (literal %)
fn builtin_format(args: &[KlujurVal]) -> Result<KlujurVal> {
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
// Metadata Functions
// ============================================================================

/// (meta obj) - Returns the metadata of obj, or nil if there is none.
fn builtin_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("meta", 1, args.len()));
    }
    match &args[0] {
        // For values with inline metadata
        KlujurVal::Symbol(_, meta)
        | KlujurVal::List(_, meta)
        | KlujurVal::Vector(_, meta)
        | KlujurVal::Map(_, meta)
        | KlujurVal::Set(_, meta) => match meta {
            Some(m) => Ok(KlujurVal::Map((**m).clone(), None)),
            None => Ok(KlujurVal::Nil),
        },
        // For vars, get var metadata
        KlujurVal::Var(v) => match v.meta() {
            Some(m) => Ok(KlujurVal::Map(m, None)),
            None => Ok(KlujurVal::Nil),
        },
        // Other types don't support metadata
        _ => Ok(KlujurVal::Nil),
    }
}

/// (with-meta obj m) - Returns obj with metadata m.
fn builtin_with_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("with-meta", 2, args.len()));
    }
    let meta_map = match &args[1] {
        KlujurVal::Map(m, _) => Some(Rc::new(m.clone())),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::type_error_in(
                "with-meta",
                "map or nil",
                other.type_name(),
            ));
        }
    };
    match args[0].with_meta(meta_map) {
        Some(val) => Ok(val),
        None => Err(Error::EvalError(format!(
            "with-meta: {} doesn't support metadata",
            args[0].type_name()
        ))),
    }
}

/// (vary-meta obj f & args) - Returns obj with (apply f (meta obj) args) as metadata.
/// Note: This is a simplified version that doesn't support extra args (requires apply).
fn builtin_vary_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::AtLeast(2),
            got: args.len(),
            name: Some("vary-meta".into()),
        });
    }
    // vary-meta requires calling f - this needs access to apply/eval
    // For now, we'll return an error suggesting use of with-meta directly
    // A full implementation would need to be in eval.rs or receive an eval context
    Err(Error::EvalError(
        "vary-meta: not yet implemented (use with-meta with explicit meta manipulation)".into(),
    ))
}

/// (alter-meta! ref f & args) - Atomically alters ref's metadata.
fn builtin_alter_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::AtLeast(2),
            got: args.len(),
            name: Some("alter-meta!".into()),
        });
    }
    // alter-meta! requires calling f - this needs access to apply/eval
    Err(Error::EvalError(
        "alter-meta!: not yet implemented (use reset-meta! for direct assignment)".into(),
    ))
}

/// (reset-meta! ref m) - Sets ref's metadata to m.
fn builtin_reset_meta(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("reset-meta!", 2, args.len()));
    }
    let meta_map = match &args[1] {
        KlujurVal::Map(m, _) => Some(m.clone()),
        KlujurVal::Nil => None,
        other => {
            return Err(Error::type_error_in(
                "reset-meta!",
                "map or nil",
                other.type_name(),
            ));
        }
    };
    match &args[0] {
        KlujurVal::Var(v) => {
            v.set_meta(meta_map.clone());
            // Return the new metadata (or nil)
            match meta_map {
                Some(m) => Ok(KlujurVal::Map(m, None)),
                None => Ok(KlujurVal::Nil),
            }
        }
        KlujurVal::Atom(_) => {
            // Atoms could also support metadata in Clojure
            Err(Error::EvalError(
                "reset-meta!: atoms don't yet support metadata".into(),
            ))
        }
        other => Err(Error::type_error_in(
            "reset-meta!",
            "var or atom",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Multimethod Functions
// ============================================================================

/// (methods multimethod) - Returns a map of dispatch value -> method function
fn builtin_methods(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::arity_named("methods", 1, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m,
        other => {
            return Err(Error::type_error_in(
                "methods",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    // Convert HashMap to OrdMap for consistent ordering
    let methods_map: OrdMap<KlujurVal, KlujurVal> = mm.get_methods().into_iter().collect();
    Ok(KlujurVal::Map(methods_map, None))
}

/// (get-method multimethod dispatch-val) - Returns the method for dispatch-val, or nil
fn builtin_get_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("get-method", 2, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m,
        other => {
            return Err(Error::type_error_in(
                "get-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    match mm.get_method(&args[1]) {
        Some(method) => Ok(method),
        None => Ok(KlujurVal::Nil),
    }
}

/// (remove-method multimethod dispatch-val) - Removes the method for dispatch-val
fn builtin_remove_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::arity_named("remove-method", 2, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "remove-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    mm.remove_method(&args[1]);
    Ok(KlujurVal::Multimethod(mm))
}

/// (prefer-method multimethod preferred-val other-val) - Set preference for ambiguous dispatch
fn builtin_prefer_method(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 3 {
        return Err(Error::arity_named("prefer-method", 3, args.len()));
    }
    let mm = match &args[0] {
        KlujurVal::Multimethod(m) => m.clone(),
        other => {
            return Err(Error::type_error_in(
                "prefer-method",
                "multimethod",
                other.type_name(),
            ));
        }
    };
    mm.prefer_method(args[1].clone(), args[2].clone());
    Ok(KlujurVal::Multimethod(mm))
}

// ============================================================================
// Hierarchy Functions
// ============================================================================

/// (make-hierarchy) - Creates a new, independent, hierarchy
fn builtin_make_hierarchy(args: &[KlujurVal]) -> Result<KlujurVal> {
    if !args.is_empty() {
        return Err(Error::arity_named("make-hierarchy", 0, args.len()));
    }
    Ok(KlujurVal::Hierarchy(Rc::new(RefCell::new(
        KlujurHierarchy::new(),
    ))))
}

/// (isa? child parent) - Returns true if child is derived from parent (using global hierarchy)
/// (isa? h child parent) - Returns true if child is derived from parent (using hierarchy h)
fn builtin_isa(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        2 => {
            // (isa? child parent) - uses global hierarchy
            // For now, just do equality check since we don't have access to global hierarchy here
            // The derive/isa? with global hierarchy requires special form access to env
            let child = &args[0];
            let parent = &args[1];
            // Without global hierarchy, isa? is just equality for non-hierarchy version
            // This will be enhanced when called from eval with env access
            Ok(KlujurVal::Bool(child == parent))
        }
        3 => {
            // (isa? h child parent) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in("isa?", "hierarchy", other.type_name()));
                }
            };
            let child = &args[1];
            let parent = &args[2];
            Ok(KlujurVal::Bool(h.borrow().isa(child, parent)))
        }
        n => Err(Error::EvalError(format!(
            "isa? expects 2 or 3 arguments, got {}",
            n
        ))),
    }
}

/// (parents child) - Returns the immediate parents of child (using global hierarchy)
/// (parents h child) - Returns the immediate parents of child (using hierarchy h)
fn builtin_parents(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (parents child) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (parents h child) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "parents",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let child = &args[1];
            let parents = h.borrow().parents(child);
            Ok(KlujurVal::set(parents.into_iter().collect()))
        }
        n => Err(Error::EvalError(format!(
            "parents expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

/// (ancestors child) - Returns all ancestors of child (using global hierarchy)
/// (ancestors h child) - Returns all ancestors of child (using hierarchy h)
fn builtin_ancestors(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (ancestors child) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (ancestors h child) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "ancestors",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let child = &args[1];
            let ancestors = h.borrow().ancestors(child);
            Ok(KlujurVal::set(ancestors.into_iter().collect()))
        }
        n => Err(Error::EvalError(format!(
            "ancestors expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

/// (descendants parent) - Returns all descendants of parent (using global hierarchy)
/// (descendants h parent) - Returns all descendants of parent (using hierarchy h)
fn builtin_descendants(args: &[KlujurVal]) -> Result<KlujurVal> {
    match args.len() {
        1 => {
            // (descendants parent) - uses global hierarchy
            // Without env access, return empty set
            Ok(KlujurVal::empty_set())
        }
        2 => {
            // (descendants h parent) - uses provided hierarchy
            let h = match &args[0] {
                KlujurVal::Hierarchy(h) => h.clone(),
                other => {
                    return Err(Error::type_error_in(
                        "descendants",
                        "hierarchy",
                        other.type_name(),
                    ));
                }
            };
            let parent = &args[1];
            let descendants = h.borrow().descendants(parent);
            Ok(KlujurVal::set(descendants.into_iter().collect()))
        }
        n => Err(Error::EvalError(format!(
            "descendants expects 1 or 2 arguments, got {}",
            n
        ))),
    }
}

// ============================================================================
// Transducers - Reduced Type
// ============================================================================

/// (reduced x) - Wrap x in a Reduced marker for early termination in transducers
fn builtin_reduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("reduced".into()),
        });
    }
    Ok(KlujurVal::reduced(args[0].clone()))
}

/// (reduced? x) - Returns true if x is a Reduced value
fn builtin_reduced_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("reduced?".into()),
        });
    }
    Ok(KlujurVal::Bool(matches!(&args[0], KlujurVal::Reduced(_))))
}

/// (unreduced x) - If x is Reduced, unwrap it; otherwise return x unchanged
fn builtin_unreduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("unreduced".into()),
        });
    }
    match &args[0] {
        KlujurVal::Reduced(v) => Ok((**v).clone()),
        v => Ok(v.clone()),
    }
}

/// (ensure-reduced x) - If x is not already Reduced, wrap it; otherwise return x
fn builtin_ensure_reduced(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("ensure-reduced".into()),
        });
    }
    match &args[0] {
        KlujurVal::Reduced(_) => Ok(args[0].clone()),
        v => Ok(KlujurVal::reduced(v.clone())),
    }
}

// ============================================================================
// Volatiles - Lightweight Mutable State for Transducers
// ============================================================================

/// (volatile! x) - Create a volatile with initial value x
fn builtin_volatile(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("volatile!".into()),
        });
    }
    Ok(KlujurVal::volatile(args[0].clone()))
}

/// (volatile? x) - Returns true if x is a Volatile
fn builtin_volatile_p(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 1 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(1),
            got: args.len(),
            name: Some("volatile?".into()),
        });
    }
    Ok(KlujurVal::Bool(matches!(&args[0], KlujurVal::Volatile(_))))
}

/// (vreset! vol newval) - Set volatile's value to newval, returns newval
fn builtin_vreset(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() != 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::Exact(2),
            got: args.len(),
            name: Some("vreset!".into()),
        });
    }
    match &args[0] {
        KlujurVal::Volatile(v) => Ok(v.reset(args[1].clone())),
        other => Err(Error::type_error_in(
            "vreset!",
            "volatile",
            other.type_name(),
        )),
    }
}

/// (vswap! vol f & args) - Atomically swaps value of volatile to (apply f current-value args)
fn builtin_vswap(args: &[KlujurVal]) -> Result<KlujurVal> {
    if args.len() < 2 {
        return Err(Error::ArityError {
            expected: crate::error::AritySpec::AtLeast(2),
            got: args.len(),
            name: Some("vswap!".into()),
        });
    }
    let vol = match &args[0] {
        KlujurVal::Volatile(v) => v,
        other => {
            return Err(Error::type_error_in(
                "vswap!",
                "volatile",
                other.type_name(),
            ));
        }
    };
    let f = &args[1];

    // Get current value
    let old_val = vol.deref();

    // Build args: [old-val, ...extra-args]
    let mut call_args = vec![old_val];
    call_args.extend(args[2..].iter().cloned());

    // Apply f
    let new_val = apply(f, &call_args)?;

    // Set and return
    Ok(vol.reset(new_val))
}

// ============================================================================
// Transducers - Execution
// ============================================================================

/// (transduce xform f coll)
/// (transduce xform f init coll)
/// Reduce with transducer. Applies xform to f to get transformed reducing function,
/// then reduces coll with it. Handles early termination via Reduced.
fn builtin_transduce(args: &[KlujurVal]) -> Result<KlujurVal> {
    let (xform, f, init, coll) = match args.len() {
        3 => {
            // (transduce xform f coll) - get init by calling (f)
            let xform = &args[0];
            let f = &args[1];
            let coll = &args[2];
            let init = apply(f, &[])?;
            (xform, f, init, coll)
        }
        4 => {
            // (transduce xform f init coll)
            (&args[0], &args[1], args[2].clone(), &args[3])
        }
        _ => {
            return Err(Error::ArityError {
                expected: crate::error::AritySpec::Range(3, 4),
                got: args.len(),
                name: Some("transduce".into()),
            });
        }
    };

    // Apply transducer to get transformed reducing function
    // xf = (xform f)
    let xf = apply(xform, std::slice::from_ref(f))?;

    // Get sequence from collection
    let items = to_seq(coll)?;

    // Reduce with transformed function
    let mut result = init;
    for item in items {
        result = apply(&xf, &[result, item])?;
        // Check for early termination with Reduced
        if let KlujurVal::Reduced(v) = result {
            result = (*v).clone();
            break;
        }
    }

    // Call completion arity: (xf result)
    apply(&xf, &[result])
}
