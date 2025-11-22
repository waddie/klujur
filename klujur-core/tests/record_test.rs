// klujur-core - Record integration tests
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Integration tests for Klujur records.
//!
//! Tests for: defrecord, constructors, field access, assoc/dissoc/get,
//! equality, type function, inline protocols, seq operations

use klujur_core::builtins::register_builtins;
use klujur_core::env::Env;
use klujur_core::eval::eval;
use klujur_parser::{KlujurVal, Parser};

/// Helper to evaluate multiple expressions in shared env and return the last result.
fn eval_forms(forms: &[&str]) -> Result<KlujurVal, String> {
    let env = Env::new();
    register_builtins(&env);
    eval_forms_with_env(forms, &env)
}

fn eval_forms_with_env(forms: &[&str], env: &Env) -> Result<KlujurVal, String> {
    let mut result = KlujurVal::Nil;
    for form in forms {
        let mut parser = Parser::new(form).map_err(|e| e.to_string())?;
        if let Some(expr) = parser.parse().map_err(|e| e.to_string())? {
            result = eval(&expr, env).map_err(|e| e.to_string())?;
        }
    }
    Ok(result)
}

/// Assert that evaluating forms produces the expected value.
macro_rules! assert_eval_forms {
    ($forms:expr, $expected:expr) => {
        let result = eval_forms($forms);
        assert!(
            result.is_ok(),
            "Failed to evaluate forms: {:?}",
            result.err()
        );
        assert_eq!(
            result.unwrap(),
            $expected,
            "Evaluation did not match expected"
        );
    };
}

// =============================================================================
// Basic defrecord
// =============================================================================

#[test]
fn test_defrecord_basic() {
    let result = eval_forms(&["(defrecord Person [name age])"]);
    assert!(result.is_ok());
    // defrecord returns the record name symbol
    assert_eq!(result.unwrap().to_string(), "Person");
}

#[test]
fn test_defrecord_creates_positional_constructor() {
    assert_eval_forms!(
        &["(defrecord Person [name age])", "(fn? ->Person)",],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_defrecord_creates_map_constructor() {
    assert_eval_forms!(
        &["(defrecord Person [name age])", "(fn? map->Person)",],
        KlujurVal::Bool(true)
    );
}

// =============================================================================
// Positional Constructor
// =============================================================================

#[test]
fn test_positional_constructor() {
    let result = eval_forms(&["(defrecord Person [name age])", "(->Person \"Alice\" 30)"]);
    assert!(result.is_ok());
    let record = result.unwrap();
    // Record should print in the format #Person{:name "Alice", :age 30}
    assert!(record.to_string().contains("Person"));
    assert!(record.to_string().contains("Alice"));
}

#[test]
fn test_positional_constructor_arity_error() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(->Person \"Alice\")", // Missing age
    ]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("arity") || err.contains("argument"));
}

// =============================================================================
// Map Constructor
// =============================================================================

#[test]
fn test_map_constructor() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(map->Person {:name \"Bob\" :age 25})",
    ]);
    assert!(result.is_ok());
    let record = result.unwrap();
    assert!(record.to_string().contains("Person"));
    assert!(record.to_string().contains("Bob"));
}

#[test]
fn test_map_constructor_missing_field_error() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(map->Person {:name \"Bob\"})", // Missing age
    ]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("Missing field") || err.contains("age"));
}

#[test]
fn test_map_constructor_with_extra_fields() {
    // Extra fields should be included
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (map->Person {:name \"Charlie\" :age 35 :city \"London\"}))",
            "(:city p)",
        ],
        KlujurVal::string("London")
    );
}

// =============================================================================
// Keyword Field Access
// =============================================================================

#[test]
fn test_keyword_access_name() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(:name p)",
        ],
        KlujurVal::string("Alice")
    );
}

#[test]
fn test_keyword_access_age() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(:age p)",
        ],
        KlujurVal::int(30)
    );
}

#[test]
fn test_keyword_access_missing_key_returns_nil() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(:city p)",
        ],
        KlujurVal::Nil
    );
}

#[test]
fn test_keyword_access_missing_key_with_default() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(:city p \"Unknown\")",
        ],
        KlujurVal::string("Unknown")
    );
}

// =============================================================================
// get function
// =============================================================================

#[test]
fn test_get_on_record() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(get p :name)",
        ],
        KlujurVal::string("Alice")
    );
}

#[test]
fn test_get_on_record_missing_key() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(get p :city)",
        ],
        KlujurVal::Nil
    );
}

#[test]
fn test_get_on_record_missing_key_with_default() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(get p :city \"N/A\")",
        ],
        KlujurVal::string("N/A")
    );
}

// =============================================================================
// assoc on Records
// =============================================================================

#[test]
fn test_assoc_updates_field() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def p2 (assoc p :age 31))",
            "(:age p2)",
        ],
        KlujurVal::int(31)
    );
}

#[test]
fn test_assoc_preserves_type() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def p2 (assoc p :age 31))",
            "(= (type p) (type p2))",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_assoc_adds_extra_field() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def p2 (assoc p :city \"London\"))",
            "(:city p2)",
        ],
        KlujurVal::string("London")
    );
}

#[test]
fn test_assoc_extra_field_preserves_type() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def p2 (assoc p :city \"London\"))",
            "(= (type p) (type p2))",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_assoc_multiple_fields() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def p2 (assoc p :age 31 :city \"Paris\"))",
            "(+ (:age p2) (count (:city p2)))",
        ],
        KlujurVal::int(36) // 31 + 5
    );
}

// =============================================================================
// dissoc on Records
// =============================================================================

#[test]
fn test_dissoc_extra_field_returns_record() {
    // Dissoc of extra field should preserve record type
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(def p (assoc (->Person \"Alice\" 30) :city \"London\"))",
        "(def p2 (dissoc p :city))",
        "(type p2)",
    ]);
    assert!(result.is_ok());
    // Should still be Person type
    assert_eq!(result.unwrap().to_string(), "Person");
}

#[test]
fn test_dissoc_base_field_returns_map() {
    // Dissoc of base field should return a map
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(def p (->Person \"Alice\" 30))",
        "(def m (dissoc p :name))",
        "(type m)",
    ]);
    assert!(result.is_ok());
    // Should now be a map (type returns String "map")
    assert_eq!(result.unwrap(), KlujurVal::string("map"));
}

#[test]
fn test_dissoc_base_field_preserves_remaining_values() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(def m (dissoc p :name))",
            "(:age m)",
        ],
        KlujurVal::int(30)
    );
}

// =============================================================================
// Record Equality
// =============================================================================

#[test]
fn test_records_equal_same_values() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(= (->Person \"Alice\" 30) (->Person \"Alice\" 30))",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_records_not_equal_different_values() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(= (->Person \"Alice\" 30) (->Person \"Bob\" 30))",
        ],
        KlujurVal::Bool(false)
    );
}

#[test]
fn test_records_not_equal_to_map() {
    // Records should NOT equal maps with same keys/values
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(= (->Person \"Alice\" 30) {:name \"Alice\" :age 30})",
        ],
        KlujurVal::Bool(false)
    );
}

#[test]
fn test_different_record_types_not_equal() {
    // Different record types should not be equal even with same values
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(defrecord Employee [name age])",
            "(= (->Person \"Alice\" 30) (->Employee \"Alice\" 30))",
        ],
        KlujurVal::Bool(false)
    );
}

// =============================================================================
// type function
// =============================================================================

#[test]
fn test_type_returns_record_name() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(= (type p) 'Person)",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_type_of_different_records() {
    let env = Env::new();
    register_builtins(&env);

    eval_forms_with_env(
        &[
            "(defrecord Person [name age])",
            "(defrecord Product [name price])",
        ],
        &env,
    )
    .unwrap();

    let person_type = eval_forms_with_env(&["(type (->Person \"Alice\" 30))"], &env).unwrap();
    let product_type = eval_forms_with_env(&["(type (->Product \"Widget\" 9.99))"], &env).unwrap();

    assert_eq!(person_type.to_string(), "Person");
    assert_eq!(product_type.to_string(), "Product");
}

// =============================================================================
// Seq operations (keys, vals, count)
// =============================================================================

#[test]
fn test_keys_on_record() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(def p (->Person \"Alice\" 30))",
        "(count (keys p))",
    ]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), KlujurVal::int(2));
}

#[test]
fn test_vals_on_record() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(def p (->Person \"Alice\" 30))",
        "(count (vals p))",
    ]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), KlujurVal::int(2));
}

#[test]
fn test_count_on_record() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person \"Alice\" 30))",
            "(count p)",
        ],
        KlujurVal::int(2)
    );
}

#[test]
fn test_count_on_record_with_extra_fields() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (assoc (->Person \"Alice\" 30) :city \"London\"))",
            "(count p)",
        ],
        KlujurVal::int(3)
    );
}

#[test]
fn test_seq_on_record() {
    let result = eval_forms(&[
        "(defrecord Person [name age])",
        "(def p (->Person \"Alice\" 30))",
        "(seq? (seq p))",
    ]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), KlujurVal::Bool(true));
}

// =============================================================================
// Inline Protocol Implementations
// =============================================================================

#[test]
fn test_defrecord_with_inline_protocol() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]))",
            "(defrecord Product [name price]
               Describable
               (describe [p] (str (:name p) \" costs $\" (:price p))))",
            "(describe (->Product \"Widget\" 9.99))",
        ],
        KlujurVal::string("Widget costs $9.99")
    );
}

#[test]
fn test_defrecord_with_multiple_protocol_methods() {
    assert_eval_forms!(
        &[
            "(defprotocol Printable
               (to-string [x])
               (to-short-string [x]))",
            "(defrecord Point [x y]
               Printable
               (to-string [p] (str \"(\" (:x p) \", \" (:y p) \")\"))
               (to-short-string [p] (str (:x p) \",\" (:y p))))",
            "(to-string (->Point 3 4))",
        ],
        KlujurVal::string("(3, 4)")
    );
}

#[test]
fn test_defrecord_with_multiple_protocols() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]))",
            "(defprotocol Printable (to-string [x]))",
            "(defrecord Item [name value]
               Describable
               (describe [i] (str \"Item: \" (:name i)))
               Printable
               (to-string [i] (str (:name i) \"=\" (:value i))))",
            "(to-string (->Item \"foo\" 42))",
        ],
        KlujurVal::string("foo=42")
    );
}

#[test]
fn test_protocol_satisfies_for_record() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]))",
            "(defrecord Product [name price]
               Describable
               (describe [p] \"A product\"))",
            "(satisfies? Describable (->Product \"Widget\" 9.99))",
        ],
        KlujurVal::Bool(true)
    );
}

#[test]
fn test_protocol_not_satisfies_for_record_without_impl() {
    assert_eval_forms!(
        &[
            "(defprotocol Describable (describe [x]))",
            "(defprotocol Printable (to-string [x]))",
            "(defrecord Product [name price]
               Describable
               (describe [p] \"A product\"))",
            "(satisfies? Printable (->Product \"Widget\" 9.99))",
        ],
        KlujurVal::Bool(false)
    );
}

// =============================================================================
// Record Printing
// =============================================================================

#[test]
fn test_record_print_format() {
    let result = eval_forms(&["(defrecord Person [name age])", "(->Person \"Alice\" 30)"]);
    assert!(result.is_ok());
    let output = result.unwrap().to_string();
    // Should contain the record type indicator
    assert!(output.contains("Person"));
    // Should contain the field names
    assert!(output.contains(":name") || output.contains("name"));
    assert!(output.contains(":age") || output.contains("age"));
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_record_with_single_field() {
    assert_eval_forms!(
        &[
            "(defrecord Wrapper [value])",
            "(def w (->Wrapper 42))",
            "(:value w)",
        ],
        KlujurVal::int(42)
    );
}

#[test]
fn test_record_with_many_fields() {
    assert_eval_forms!(
        &[
            "(defrecord Entity [a b c d e])",
            "(def e (->Entity 1 2 3 4 5))",
            "(+ (:a e) (:b e) (:c e) (:d e) (:e e))",
        ],
        KlujurVal::int(15)
    );
}

#[test]
fn test_record_field_with_nil_value() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def p (->Person nil 30))",
            "(:name p)",
        ],
        KlujurVal::Nil
    );
}

#[test]
fn test_record_as_map_value() {
    // Records should work as values in other data structures
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def people {:alice (->Person \"Alice\" 30)})",
            "(:name (:alice people))",
        ],
        KlujurVal::string("Alice")
    );
}

#[test]
fn test_record_in_vector() {
    assert_eval_forms!(
        &[
            "(defrecord Person [name age])",
            "(def people [(->Person \"Alice\" 30) (->Person \"Bob\" 25)])",
            "(:name (first people))",
        ],
        KlujurVal::string("Alice")
    );
}
