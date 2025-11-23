// klujur-embed integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Comprehensive tests for the klujur-embed embedding API.

use klujur_embed::{Engine, Error, FromKlujurVal, KlujurVal, Result};

// =============================================================================
// Type Conversion Edge Cases (boundary values)
// =============================================================================

mod type_conversion {
    use super::*;

    #[test]
    fn int_boundary_values() {
        let engine = Engine::new().unwrap();

        // i64 max
        let max_result = engine.eval(&format!("{}", i64::MAX)).unwrap();
        let max_val: i64 = i64::from_klujur_val(&max_result).unwrap();
        assert_eq!(max_val, i64::MAX);

        // i64 min - cannot be parsed directly as literal since parsing uses negation
        // which overflows. Instead, use arithmetic: (- -1 i64::MAX)
        let min_result = engine.eval(&format!("(- -1 {})", i64::MAX)).unwrap();
        let min_val: i64 = i64::from_klujur_val(&min_result).unwrap();
        assert_eq!(min_val, i64::MIN);
    }

    #[test]
    fn float_boundary_values() {
        let engine = Engine::new().unwrap();

        // Test infinity
        let inf_result = engine.eval("(/ 1.0 0.0)").unwrap();
        let inf_val: f64 = f64::from_klujur_val(&inf_result).unwrap();
        assert!(inf_val.is_infinite() && inf_val.is_sign_positive());

        let neg_inf_result = engine.eval("(/ -1.0 0.0)").unwrap();
        let neg_inf_val: f64 = f64::from_klujur_val(&neg_inf_result).unwrap();
        assert!(neg_inf_val.is_infinite() && neg_inf_val.is_sign_negative());
    }

    #[test]
    fn f32_overflow_detection() {
        // Test that converting a huge f64 to f32 produces an error
        let val = KlujurVal::float(f64::MAX);
        let result = f32::from_klujur_val(&val);
        assert!(result.is_err());
    }

    #[test]
    fn string_empty_and_unicode() {
        let engine = Engine::new().unwrap();

        // Empty string
        engine.set("empty", "");
        let empty: String = engine.get_as::<String>("empty").unwrap();
        assert_eq!(empty, "");

        // Unicode
        engine.set("unicode", "Hello, 世界! 🎉");
        let unicode: String = engine.get_as::<String>("unicode").unwrap();
        assert_eq!(unicode, "Hello, 世界! 🎉");
    }
}

// =============================================================================
// Engine::new_bare() behaviour
// =============================================================================

mod new_bare {
    use super::*;

    #[test]
    fn new_bare_creates_minimal_engine() {
        let engine = Engine::new_bare();

        // Should have basic special forms
        let result = engine.eval("(if true 1 2)");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().to_string(), "1");
    }

    #[test]
    fn new_bare_no_stdlib() {
        let engine = Engine::new_bare();

        // Stdlib-only symbols should not exist in bare engine
        // 'for' is definitely stdlib - should fail to resolve
        let for_result = engine.eval("for");
        // for is definitely stdlib - should fail
        assert!(for_result.is_err() || matches!(for_result.unwrap(), KlujurVal::Nil));
    }
}

// =============================================================================
// Engine::eval_file() error handling
// =============================================================================

mod eval_file {
    use super::*;
    use std::fs;

    #[test]
    fn eval_file_nonexistent() {
        let engine = Engine::new().unwrap();
        let result = engine.eval_file("/nonexistent/path/to/file.klj");
        assert!(result.is_err());
    }

    #[test]
    fn eval_file_valid() {
        let engine = Engine::new().unwrap();

        // Create temp file
        let temp_path = "/tmp/klujur_test_eval_file.klj";
        fs::write(temp_path, "(+ 1 2 3)").unwrap();

        let result = engine.eval_file(temp_path);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().to_string(), "6");

        fs::remove_file(temp_path).ok();
    }

    #[test]
    fn eval_file_syntax_error() {
        let engine = Engine::new().unwrap();

        let temp_path = "/tmp/klujur_test_syntax_error.klj";
        fs::write(temp_path, "(+ 1 2").unwrap(); // Missing closing paren

        let result = engine.eval_file(temp_path);
        assert!(result.is_err());

        fs::remove_file(temp_path).ok();
    }
}

// =============================================================================
// Engine::get()/get_as() with undefined symbols
// =============================================================================

mod get_undefined {
    use super::*;

    #[test]
    fn get_undefined_symbol_returns_none() {
        let engine = Engine::new().unwrap();
        let result = engine.get("nonexistent_symbol_xyz");
        assert!(result.is_none());
    }

    #[test]
    fn get_as_undefined_symbol_returns_none() {
        let engine = Engine::new().unwrap();
        let result: Option<i64> = engine.get_as("nonexistent_symbol_xyz");
        assert!(result.is_none());
    }

    #[test]
    fn get_after_def() {
        let engine = Engine::new().unwrap();
        engine.eval("(def my-value 42)").unwrap();
        let result = engine.get("my-value");
        assert!(result.is_some());
        assert_eq!(result.unwrap().to_string(), "42");
    }
}

// =============================================================================
// Engine::call() with non-callable values
// =============================================================================

mod call_non_callable {
    use super::*;

    #[test]
    fn call_non_callable_int() {
        let engine = Engine::new().unwrap();
        engine.eval("(def not-a-fn 42)").unwrap();
        let result = engine.call("not-a-fn", &[]);
        assert!(result.is_err());
    }

    #[test]
    fn call_non_callable_string() {
        let engine = Engine::new().unwrap();
        engine.eval("(def str-val \"hello\")").unwrap();
        let result = engine.call("str-val", &[]);
        assert!(result.is_err());
    }

    #[test]
    fn call_undefined_symbol() {
        let engine = Engine::new().unwrap();
        let result = engine.call("undefined_function", &[]);
        assert!(result.is_err());
    }

    #[test]
    fn call_valid_function() {
        let engine = Engine::new().unwrap();
        let result = engine.call("+", &[KlujurVal::int(1), KlujurVal::int(2)]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().to_string(), "3");
    }
}

// =============================================================================
// register_native function registration
// =============================================================================

mod register_native {
    use super::*;

    #[test]
    fn register_simple_function() {
        let engine = Engine::new().unwrap();
        engine.register_native("my-double", |args: &[KlujurVal]| -> Result<KlujurVal> {
            match args.first() {
                Some(KlujurVal::Int(n)) => Ok(KlujurVal::int(n * 2)),
                _ => Err(Error::type_error("integer", "other")),
            }
        });

        let result = engine.eval("(my-double 21)").unwrap();
        assert_eq!(result.to_string(), "42");
    }

    #[test]
    fn register_function_with_closure() {
        let engine = Engine::new().unwrap();
        let multiplier = 10;
        engine.register_native(
            "times-ten",
            move |args: &[KlujurVal]| -> Result<KlujurVal> {
                match args.first() {
                    Some(KlujurVal::Int(n)) => Ok(KlujurVal::int(n * multiplier)),
                    _ => Err(Error::type_error("integer", "other")),
                }
            },
        );

        let result = engine.eval("(times-ten 5)").unwrap();
        assert_eq!(result.to_string(), "50");
    }

    #[test]
    fn register_overrides_existing() {
        let engine = Engine::new().unwrap();

        // First registration
        engine.register_native("my-fn", |_args: &[KlujurVal]| -> Result<KlujurVal> {
            Ok(KlujurVal::int(1))
        });
        assert_eq!(engine.eval("(my-fn)").unwrap().to_string(), "1");

        // Override
        engine.register_native("my-fn", |_args: &[KlujurVal]| -> Result<KlujurVal> {
            Ok(KlujurVal::int(2))
        });
        assert_eq!(engine.eval("(my-fn)").unwrap().to_string(), "2");
    }
}

// =============================================================================
// Option<T> conversion round-trip
// =============================================================================

mod option_conversion {
    use super::*;

    #[test]
    fn option_some_round_trip() {
        let engine = Engine::new().unwrap();

        // Some -> KlujurVal -> back
        let some_val: Option<i64> = Some(42);
        engine.set("opt-some", some_val);

        let result = engine.get("opt-some").unwrap();
        assert_eq!(result.to_string(), "42");

        let back: Option<i64> = Option::<i64>::from_klujur_val(&result).unwrap();
        assert_eq!(back, Some(42));
    }

    #[test]
    fn option_none_round_trip() {
        let engine = Engine::new().unwrap();

        let none_val: Option<i64> = None;
        engine.set("opt-none", none_val);

        let result = engine.get("opt-none").unwrap();
        assert!(matches!(result, KlujurVal::Nil));

        let back: Option<i64> = Option::<i64>::from_klujur_val(&result).unwrap();
        assert_eq!(back, None);
    }
}

// =============================================================================
// Vec<T> with nested types
// =============================================================================

mod vec_nested {
    use super::*;

    #[test]
    fn vec_of_ints() {
        let engine = Engine::new().unwrap();

        let vec: Vec<i64> = vec![1, 2, 3, 4, 5];
        engine.set("int-vec", vec);

        let result = engine.eval("int-vec").unwrap();
        assert_eq!(result.to_string(), "[1 2 3 4 5]");

        let back: Vec<i64> = Vec::<i64>::from_klujur_val(&result).unwrap();
        assert_eq!(back, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn vec_of_strings() {
        let engine = Engine::new().unwrap();

        let vec: Vec<String> = vec!["a".into(), "b".into(), "c".into()];
        engine.set("str-vec", vec);

        let result = engine.eval("str-vec").unwrap();
        let back: Vec<String> = Vec::<String>::from_klujur_val(&result).unwrap();
        assert_eq!(back, vec!["a", "b", "c"]);
    }

    #[test]
    fn vec_of_vecs() {
        let engine = Engine::new().unwrap();

        let nested: Vec<Vec<i64>> = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
        engine.set("nested", nested);

        let result = engine.eval("nested").unwrap();
        let back: Vec<Vec<i64>> = Vec::<Vec<i64>>::from_klujur_val(&result).unwrap();
        assert_eq!(back, vec![vec![1, 2], vec![3, 4], vec![5, 6]]);
    }
}

// =============================================================================
// Additional Engine functionality tests
// =============================================================================

mod engine_additional {
    use super::*;

    #[test]
    fn set_and_get_multiple_types() {
        let engine = Engine::new().unwrap();

        engine.set("int-val", 42i64);
        engine.set("float-val", 3.14f64);
        engine.set("bool-val", true);
        engine.set("str-val", "hello");

        assert_eq!(engine.get_as::<i64>("int-val").unwrap(), 42);
        assert!((engine.get_as::<f64>("float-val").unwrap() - 3.14).abs() < 0.001);
        assert!(engine.get_as::<bool>("bool-val").unwrap());
        assert_eq!(engine.get_as::<String>("str-val").unwrap(), "hello");
    }

    #[test]
    fn namespace_switching() {
        let engine = Engine::new().unwrap();

        // Start in user namespace
        engine.eval("(def x 1)").unwrap();

        // Switch to test namespace
        engine.set_namespace("test");
        engine.eval("(def x 2)").unwrap();

        // Verify values are separate
        let test_x = engine.eval("x").unwrap();
        assert_eq!(test_x.to_string(), "2");

        engine.set_namespace("user");
        let user_x = engine.eval("x").unwrap();
        assert_eq!(user_x.to_string(), "1");
    }
}
