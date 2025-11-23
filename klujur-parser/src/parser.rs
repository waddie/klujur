// klujur-parser - Parser for Klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Recursive descent parser for Klujur source code.
//!
//! Converts tokens into `KlujurVal` AST nodes.

use std::fmt;

use crate::keyword::Keyword;
use crate::lexer::{Lexer, LexerError, Token};
use crate::symbol::Symbol;
use crate::value::KlujurVal;

/// Parser error with position information.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Parse error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

impl From<LexerError> for ParseError {
    fn from(e: LexerError) -> Self {
        ParseError {
            message: e.message,
            line: e.line,
            column: e.column,
        }
    }
}

/// The parser converts tokens into `KlujurVal` AST nodes.
pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    line: usize,
    column: usize,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given source code.
    pub fn new(source: &'a str) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(source);
        // Capture position before first token
        let line = lexer.line();
        let column = lexer.column();
        let current = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current,
            line,
            column,
        })
    }

    /// Parse a single form from the source.
    /// Returns None if at end of input.
    pub fn parse(&mut self) -> Result<Option<KlujurVal>, ParseError> {
        if matches!(self.current, Token::Eof) {
            return Ok(None);
        }
        let val = self.parse_form()?;
        Ok(Some(val))
    }

    /// Parse all forms from the source.
    pub fn parse_all(&mut self) -> Result<Vec<KlujurVal>, ParseError> {
        let mut forms = Vec::new();
        while let Some(form) = self.parse()? {
            forms.push(form);
        }
        Ok(forms)
    }

    /// Parse a string and return the first form (convenience function).
    pub fn parse_str(source: &str) -> Result<Option<KlujurVal>, ParseError> {
        let mut parser = Parser::new(source)?;
        parser.parse()
    }

    /// Parse a string and return all forms (convenience function).
    pub fn parse_all_str(source: &str) -> Result<Vec<KlujurVal>, ParseError> {
        let mut parser = Parser::new(source)?;
        parser.parse_all()
    }

    // ========================================================================
    // Internal parsing methods
    // ========================================================================

    fn advance(&mut self) -> Result<Token, ParseError> {
        let prev = std::mem::replace(&mut self.current, Token::Eof);
        // Capture position of the next token before fetching it
        self.line = self.lexer.line();
        self.column = self.lexer.column();
        self.current = self.lexer.next_token()?;
        Ok(prev)
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            message,
            line: self.line,
            column: self.column,
        }
    }

    fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        if &self.current == expected {
            self.advance()?;
            Ok(())
        } else {
            Err(self.error(format!("Expected {:?}, found {:?}", expected, self.current)))
        }
    }

    fn parse_form(&mut self) -> Result<KlujurVal, ParseError> {
        match &self.current {
            // Literals
            Token::Nil => {
                self.advance()?;
                Ok(KlujurVal::nil())
            }
            Token::True => {
                self.advance()?;
                Ok(KlujurVal::bool(true))
            }
            Token::False => {
                self.advance()?;
                Ok(KlujurVal::bool(false))
            }
            Token::Int(n) => {
                let n = *n;
                self.advance()?;
                Ok(KlujurVal::int(n))
            }
            Token::Float(n) => {
                let n = *n;
                self.advance()?;
                Ok(KlujurVal::float(n))
            }
            Token::Ratio(num, den) => {
                let num = *num;
                let den = *den;
                self.advance()?;
                Ok(KlujurVal::ratio(num, den))
            }
            Token::Char(c) => {
                let c = *c;
                self.advance()?;
                Ok(KlujurVal::char(c))
            }
            Token::String(s) => {
                let s = s.clone();
                self.advance()?;
                Ok(KlujurVal::string(s))
            }
            Token::Symbol(s) => {
                let s = s.clone();
                self.advance()?;
                Ok(KlujurVal::symbol(Symbol::parse(&s)))
            }
            Token::Keyword(s) => {
                let s = s.clone();
                self.advance()?;
                Ok(KlujurVal::keyword(Keyword::parse(&s)))
            }

            // Collections
            Token::LParen => self.parse_list(),
            Token::LBracket => self.parse_vector(),
            Token::LBrace => self.parse_map(),
            Token::Set => self.parse_set(),

            // Reader macros
            Token::Quote => self.parse_quote("quote"),
            Token::SyntaxQuote => self.parse_quote("syntax-quote"),
            Token::Unquote => self.parse_quote("unquote"),
            Token::UnquoteSplice => self.parse_quote("unquote-splicing"),
            Token::Deref => self.parse_quote("deref"),
            Token::VarQuote => self.parse_quote("var"),
            Token::AnonFn => self.parse_anon_fn(),
            Token::Discard => self.parse_discard(),
            Token::Regex => self.parse_regex(),
            Token::Meta => self.parse_meta(),

            // Unexpected tokens
            Token::RParen => Err(self.error("Unexpected ')'".to_string())),
            Token::RBracket => Err(self.error("Unexpected ']'".to_string())),
            Token::RBrace => Err(self.error("Unexpected '}'".to_string())),
            Token::Eof => Err(self.error("Unexpected end of input".to_string())),
        }
    }

    fn parse_list(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume (
        let mut elements = Vec::new();

        while !matches!(self.current, Token::RParen | Token::Eof) {
            elements.push(self.parse_form()?);
        }

        self.expect(&Token::RParen)?;
        Ok(KlujurVal::list(elements))
    }

    fn parse_vector(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume [
        let mut elements = Vec::new();

        while !matches!(self.current, Token::RBracket | Token::Eof) {
            elements.push(self.parse_form()?);
        }

        self.expect(&Token::RBracket)?;
        Ok(KlujurVal::vector(elements))
    }

    fn parse_map(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume {
        let mut pairs = Vec::new();

        while !matches!(self.current, Token::RBrace | Token::Eof) {
            let key = self.parse_form()?;
            if matches!(self.current, Token::RBrace | Token::Eof) {
                return Err(
                    self.error("Map literal must contain an even number of forms".to_string())
                );
            }
            let value = self.parse_form()?;
            pairs.push((key, value));
        }

        self.expect(&Token::RBrace)?;
        Ok(KlujurVal::map(pairs))
    }

    fn parse_set(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume #{
        let mut elements = Vec::new();

        while !matches!(self.current, Token::RBrace | Token::Eof) {
            elements.push(self.parse_form()?);
        }

        self.expect(&Token::RBrace)?;
        Ok(KlujurVal::set(elements))
    }

    fn parse_quote(&mut self, name: &str) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume the quote token
        let form = self.parse_form()?;
        Ok(KlujurVal::list(vec![
            KlujurVal::symbol(Symbol::new(name)),
            form,
        ]))
    }

    fn parse_anon_fn(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume #(

        // Collect the body forms
        let mut body = Vec::new();
        while !matches!(self.current, Token::RParen | Token::Eof) {
            body.push(self.parse_form()?);
        }
        self.expect(&Token::RParen)?;

        // Find the highest numbered argument (%, %1, %2, ..., %&)
        let (max_arg, has_rest) = Self::find_fn_args(&body);

        // Build parameter vector
        let mut params = Vec::new();
        if max_arg > 0 {
            for i in 1..=max_arg {
                params.push(KlujurVal::symbol(Symbol::new(&format!("p{}_#", i))));
            }
        }
        if has_rest {
            params.push(KlujurVal::symbol(Symbol::new("&")));
            params.push(KlujurVal::symbol(Symbol::new("rest_#")));
        }

        // Transform body, replacing % arguments with parameter names
        let transformed_body: Vec<KlujurVal> =
            body.into_iter().map(Self::transform_fn_args).collect();

        // Build (fn* [params...] (body...))
        // The body forms are wrapped in a single list (implicit do for multiple forms)
        let fn_form = vec![
            KlujurVal::symbol(Symbol::new("fn*")),
            KlujurVal::vector(params),
            KlujurVal::list(transformed_body),
        ];

        Ok(KlujurVal::list(fn_form))
    }

    fn find_fn_args(forms: &[KlujurVal]) -> (usize, bool) {
        let mut max_arg = 0usize;
        let mut has_rest = false;

        for form in forms {
            Self::find_fn_args_in_form(form, &mut max_arg, &mut has_rest);
        }

        (max_arg, has_rest)
    }

    fn find_fn_args_in_form(form: &KlujurVal, max_arg: &mut usize, has_rest: &mut bool) {
        match form {
            KlujurVal::Symbol(sym, _) => {
                let name = sym.name();
                if name == "%" {
                    *max_arg = (*max_arg).max(1);
                } else if name == "%&" {
                    *has_rest = true;
                } else if let Some(rest) = name.strip_prefix('%')
                    && let Ok(n) = rest.parse::<usize>()
                {
                    *max_arg = (*max_arg).max(n);
                }
            }
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => {
                for item in items.iter() {
                    Self::find_fn_args_in_form(item, max_arg, has_rest);
                }
            }
            KlujurVal::Map(map, _) => {
                for (k, v) in map.iter() {
                    Self::find_fn_args_in_form(k, max_arg, has_rest);
                    Self::find_fn_args_in_form(v, max_arg, has_rest);
                }
            }
            KlujurVal::Set(set, _) => {
                for item in set.iter() {
                    Self::find_fn_args_in_form(item, max_arg, has_rest);
                }
            }
            _ => {}
        }
    }

    fn transform_fn_args(form: KlujurVal) -> KlujurVal {
        match form {
            KlujurVal::Symbol(sym, meta) => {
                let name = sym.name();
                if name == "%" {
                    KlujurVal::symbol(Symbol::new("p1_#"))
                } else if name == "%&" {
                    KlujurVal::symbol(Symbol::new("rest_#"))
                } else if let Some(rest) = name.strip_prefix('%') {
                    if let Ok(n) = rest.parse::<usize>() {
                        KlujurVal::symbol(Symbol::new(&format!("p{}_#", n)))
                    } else {
                        KlujurVal::Symbol(sym, meta)
                    }
                } else {
                    KlujurVal::Symbol(sym, meta)
                }
            }
            KlujurVal::List(items, _) => {
                let transformed: Vec<_> =
                    items.iter().cloned().map(Self::transform_fn_args).collect();
                KlujurVal::list(transformed)
            }
            KlujurVal::Vector(items, _) => {
                let transformed: Vec<_> =
                    items.iter().cloned().map(Self::transform_fn_args).collect();
                KlujurVal::vector(transformed)
            }
            KlujurVal::Map(map, _) => {
                let transformed: Vec<_> = map
                    .iter()
                    .map(|(k, v)| {
                        (
                            Self::transform_fn_args(k.clone()),
                            Self::transform_fn_args(v.clone()),
                        )
                    })
                    .collect();
                KlujurVal::map(transformed)
            }
            KlujurVal::Set(set, _) => {
                let transformed: Vec<_> =
                    set.iter().cloned().map(Self::transform_fn_args).collect();
                KlujurVal::set(transformed)
            }
            other => other,
        }
    }

    fn parse_discard(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume #_
        // Parse and discard the next form
        self.parse_form()?;
        // Return the form after the discarded one
        self.parse_form()
    }

    fn parse_regex(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume the Regex token
        let pattern = self
            .lexer
            .take_regex_pattern()
            .ok_or_else(|| self.error("Missing regex pattern".to_string()))?;
        // For now, store as a list (re-pattern "...")
        // Later phases can add a proper Regex type
        Ok(KlujurVal::list(vec![
            KlujurVal::symbol(Symbol::new("re-pattern")),
            KlujurVal::string(pattern),
        ]))
    }

    fn parse_meta(&mut self) -> Result<KlujurVal, ParseError> {
        self.advance()?; // consume ^
        let raw_meta = self.parse_form()?;

        // Handle metadata shorthands per Clojure semantics:
        // ^:keyword    => {:keyword true}
        // ^Symbol      => {:tag Symbol}
        // ^"String"    => {:tag "String"}
        // ^[T1 T2]     => {:param-tags [T1 T2]}
        // ^{...}       => {...} (already a map)
        let meta = match raw_meta {
            KlujurVal::Keyword(kw) => {
                // ^:keyword => {:keyword true}
                KlujurVal::map(vec![(KlujurVal::Keyword(kw), KlujurVal::bool(true))])
            }
            KlujurVal::Symbol(sym, _) => {
                // ^Symbol => {:tag Symbol}
                KlujurVal::map(vec![(
                    KlujurVal::keyword(Keyword::new("tag")),
                    KlujurVal::Symbol(sym, None),
                )])
            }
            KlujurVal::String(s) => {
                // ^"String" => {:tag "String"}
                KlujurVal::map(vec![(
                    KlujurVal::keyword(Keyword::new("tag")),
                    KlujurVal::String(s),
                )])
            }
            KlujurVal::Vector(items, _) => {
                // ^[Type Type] => {:param-tags [Type Type]}
                KlujurVal::map(vec![(
                    KlujurVal::keyword(Keyword::new("param-tags")),
                    KlujurVal::Vector(items, None),
                )])
            }
            KlujurVal::Map(_, _) => raw_meta, // Already a map
            other => {
                return Err(self.error(format!(
                    "Metadata must be Symbol, Keyword, String, Vector or Map, got {}",
                    other.type_name()
                )));
            }
        };

        let form = self.parse_form()?;
        // Expand to (with-meta form meta)
        Ok(KlujurVal::list(vec![
            KlujurVal::symbol(Symbol::new("with-meta")),
            form,
            meta,
        ]))
    }
}

// ============================================================================
// Convenience function
// ============================================================================

/// Parse a string and return the first form.
pub fn read(source: &str) -> Result<Option<KlujurVal>, ParseError> {
    Parser::parse_str(source)
}

/// Parse a string and return all forms.
pub fn read_all(source: &str) -> Result<Vec<KlujurVal>, ParseError> {
    Parser::parse_all_str(source)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> KlujurVal {
        read(s).unwrap().unwrap()
    }

    fn parse_opt(s: &str) -> Option<KlujurVal> {
        read(s).unwrap()
    }

    #[test]
    fn test_nil() {
        assert_eq!(parse("nil"), KlujurVal::nil());
    }

    #[test]
    fn test_booleans() {
        assert_eq!(parse("true"), KlujurVal::bool(true));
        assert_eq!(parse("false"), KlujurVal::bool(false));
    }

    #[test]
    fn test_integers() {
        assert_eq!(parse("42"), KlujurVal::int(42));
        assert_eq!(parse("-1"), KlujurVal::int(-1));
        assert_eq!(parse("0xff"), KlujurVal::int(255));
    }

    #[test]
    fn test_floats() {
        assert_eq!(parse("3.14"), KlujurVal::float(3.14));
        assert_eq!(parse("1e10"), KlujurVal::float(1e10));
    }

    #[test]
    fn test_ratios() {
        assert_eq!(parse("1/2"), KlujurVal::ratio(1, 2));
        assert_eq!(parse("2/4"), KlujurVal::ratio(1, 2)); // Reduced
    }

    #[test]
    fn test_chars() {
        assert_eq!(parse(r"\a"), KlujurVal::char('a'));
        assert_eq!(parse(r"\newline"), KlujurVal::char('\n'));
    }

    #[test]
    fn test_strings() {
        assert_eq!(parse(r#""hello""#), KlujurVal::string("hello"));
        assert_eq!(
            parse(r#""hello\nworld""#),
            KlujurVal::string("hello\nworld")
        );
    }

    #[test]
    fn test_symbols() {
        let val = parse("foo");
        assert!(matches!(val, KlujurVal::Symbol(_, _)));
        if let KlujurVal::Symbol(sym, _) = val {
            assert_eq!(sym.name(), "foo");
        }
    }

    #[test]
    fn test_namespaced_symbols() {
        let val = parse("user/foo");
        if let KlujurVal::Symbol(sym, _) = val {
            assert_eq!(sym.namespace(), Some("user"));
            assert_eq!(sym.name(), "foo");
        } else {
            panic!("Expected symbol");
        }
    }

    #[test]
    fn test_keywords() {
        let val = parse(":foo");
        assert!(matches!(val, KlujurVal::Keyword(_)));
        if let KlujurVal::Keyword(kw) = val {
            assert_eq!(kw.name(), "foo");
        }
    }

    #[test]
    fn test_namespaced_keywords() {
        let val = parse(":user/foo");
        if let KlujurVal::Keyword(kw) = val {
            assert_eq!(kw.namespace(), Some("user"));
            assert_eq!(kw.name(), "foo");
        } else {
            panic!("Expected keyword");
        }
    }

    #[test]
    fn test_empty_list() {
        let val = parse("()");
        assert!(matches!(val, KlujurVal::List(..)));
        if let KlujurVal::List(items, _) = val {
            assert!(items.is_empty());
        }
    }

    #[test]
    fn test_list() {
        let val = parse("(1 2 3)");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            assert_eq!(items[0], KlujurVal::int(1));
            assert_eq!(items[1], KlujurVal::int(2));
            assert_eq!(items[2], KlujurVal::int(3));
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_empty_vector() {
        let val = parse("[]");
        assert!(matches!(val, KlujurVal::Vector(_, _)));
        if let KlujurVal::Vector(items, _) = val {
            assert!(items.is_empty());
        }
    }

    #[test]
    fn test_vector() {
        let val = parse("[1 2 3]");
        if let KlujurVal::Vector(items, _) = val {
            assert_eq!(items.len(), 3);
        } else {
            panic!("Expected vector");
        }
    }

    #[test]
    fn test_empty_map() {
        let val = parse("{}");
        assert!(matches!(val, KlujurVal::Map(_, _)));
    }

    #[test]
    fn test_map() {
        let val = parse("{:a 1 :b 2}");
        if let KlujurVal::Map(map, _) = val {
            assert_eq!(map.len(), 2);
        } else {
            panic!("Expected map");
        }
    }

    #[test]
    fn test_empty_set() {
        let val = parse("#{}");
        assert!(matches!(val, KlujurVal::Set(_, _)));
    }

    #[test]
    fn test_set() {
        let val = parse("#{1 2 3}");
        if let KlujurVal::Set(set, _) = val {
            assert_eq!(set.len(), 3);
        } else {
            panic!("Expected set");
        }
    }

    #[test]
    fn test_quote() {
        let val = parse("'foo");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 2);
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "quote");
            } else {
                panic!("Expected quote symbol");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_deref() {
        let val = parse("@x");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 2);
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "deref");
            } else {
                panic!("Expected deref symbol");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_var_quote() {
        let val = parse("#'foo");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 2);
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "var");
            } else {
                panic!("Expected var symbol");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_discard() {
        let val = parse("[1 #_2 3]");
        if let KlujurVal::Vector(items, _) = val {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], KlujurVal::int(1));
            assert_eq!(items[1], KlujurVal::int(3));
        } else {
            panic!("Expected vector");
        }
    }

    #[test]
    fn test_nested() {
        let val = parse("[[1 2] [3 4]]");
        if let KlujurVal::Vector(outer, _) = val {
            assert_eq!(outer.len(), 2);
            if let KlujurVal::Vector(inner, _) = &outer[0] {
                assert_eq!(inner.len(), 2);
            } else {
                panic!("Expected inner vector");
            }
        } else {
            panic!("Expected outer vector");
        }
    }

    #[test]
    fn test_empty_input() {
        assert!(parse_opt("").is_none());
        assert!(parse_opt("   ").is_none());
        assert!(parse_opt("; comment").is_none());
    }

    #[test]
    fn test_multiple_forms() {
        let forms = read_all("1 2 3").unwrap();
        assert_eq!(forms.len(), 3);
        assert_eq!(forms[0], KlujurVal::int(1));
        assert_eq!(forms[1], KlujurVal::int(2));
        assert_eq!(forms[2], KlujurVal::int(3));
    }

    #[test]
    fn test_anon_fn_simple() {
        let val = parse("#(+ % 1)");
        // Should be (fn* [p1_#] (+ p1_# 1))
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "fn*");
            }
            if let KlujurVal::Vector(params, _) = &items[1] {
                assert_eq!(params.len(), 1);
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_anon_fn_multiple_args() {
        let val = parse("#(+ %1 %2)");
        // Should be (fn* [p1_# p2_#] (+ p1_# p2_#))
        if let KlujurVal::List(items, _) = val {
            if let KlujurVal::Vector(params, _) = &items[1] {
                assert_eq!(params.len(), 2);
            } else {
                panic!("Expected vector params");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_anon_fn_rest_args() {
        let val = parse("#(vec %&)");
        // Should have & rest_# in params
        if let KlujurVal::List(items, _) = val {
            if let KlujurVal::Vector(params, _) = &items[1] {
                assert_eq!(params.len(), 2); // & and rest_#
            } else {
                panic!("Expected vector params");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_regex() {
        let val = parse(r#"#"pattern""#);
        // Should be (re-pattern "pattern")
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 2);
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "re-pattern");
            }
            if let KlujurVal::String(s) = &items[1] {
                assert_eq!(s.as_ref(), "pattern");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_complex_expression() {
        let val = parse("(defn foo [x] (+ x 1))");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 4);
        } else {
            panic!("Expected list");
        }
    }

    // ========================================================================
    // Metadata Tests
    // ========================================================================

    #[test]
    fn test_meta_keyword() {
        // ^:private x => (with-meta x {:private true})
        let val = parse("^:private x");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            // First item is with-meta symbol
            if let KlujurVal::Symbol(sym, _) = &items[0] {
                assert_eq!(sym.name(), "with-meta");
            } else {
                panic!("Expected symbol with-meta");
            }
            // Second item is the form (x)
            if let KlujurVal::Symbol(sym, _) = &items[1] {
                assert_eq!(sym.name(), "x");
            } else {
                panic!("Expected symbol x");
            }
            // Third item is the metadata map
            if let KlujurVal::Map(map, _) = &items[2] {
                assert_eq!(map.len(), 1);
                let private_key = KlujurVal::keyword(Keyword::new("private"));
                assert_eq!(map.get(&private_key), Some(&KlujurVal::bool(true)));
            } else {
                panic!("Expected map");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_symbol() {
        // ^String x => (with-meta x {:tag String})
        let val = parse("^String x");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            if let KlujurVal::Map(map, _) = &items[2] {
                let tag_key = KlujurVal::keyword(Keyword::new("tag"));
                let tag_val = map.get(&tag_key).unwrap();
                if let KlujurVal::Symbol(sym, _) = tag_val {
                    assert_eq!(sym.name(), "String");
                } else {
                    panic!("Expected symbol tag value");
                }
            } else {
                panic!("Expected map");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_string() {
        // ^"java.lang.String" x => (with-meta x {:tag "java.lang.String"})
        let val = parse(r#"^"java.lang.String" x"#);
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            if let KlujurVal::Map(map, _) = &items[2] {
                let tag_key = KlujurVal::keyword(Keyword::new("tag"));
                let tag_val = map.get(&tag_key).unwrap();
                if let KlujurVal::String(s) = tag_val {
                    assert_eq!(s.as_ref(), "java.lang.String");
                } else {
                    panic!("Expected string tag value");
                }
            } else {
                panic!("Expected map");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_vector() {
        // ^[long String] x => (with-meta x {:param-tags [long String]})
        let val = parse("^[long String] x");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            if let KlujurVal::Map(map, _) = &items[2] {
                let param_tags_key = KlujurVal::keyword(Keyword::new("param-tags"));
                let param_tags_val = map.get(&param_tags_key).unwrap();
                if let KlujurVal::Vector(v, _) = param_tags_val {
                    assert_eq!(v.len(), 2);
                } else {
                    panic!("Expected vector param-tags value");
                }
            } else {
                panic!("Expected map");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_map() {
        // ^{:doc "hello"} x => (with-meta x {:doc "hello"})
        let val = parse(r#"^{:doc "hello"} x"#);
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            if let KlujurVal::Map(map, _) = &items[2] {
                let doc_key = KlujurVal::keyword(Keyword::new("doc"));
                let doc_val = map.get(&doc_key).unwrap();
                if let KlujurVal::String(s) = doc_val {
                    assert_eq!(s.as_ref(), "hello");
                } else {
                    panic!("Expected string doc value");
                }
            } else {
                panic!("Expected map");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_stacked() {
        // ^:private ^:dynamic x => (with-meta (with-meta x {:dynamic true}) {:private true})
        let val = parse("^:private ^:dynamic x");
        if let KlujurVal::List(items, _) = val {
            assert_eq!(items.len(), 3);
            // The form should be another with-meta call
            if let KlujurVal::List(inner_items, _) = &items[1] {
                if let KlujurVal::Symbol(sym, _) = &inner_items[0] {
                    assert_eq!(sym.name(), "with-meta");
                }
            } else {
                panic!("Expected nested with-meta list");
            }
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_meta_invalid() {
        // ^123 x should fail - numbers aren't valid metadata
        let result = Parser::new("^123 x").unwrap().parse_all();
        assert!(result.is_err());
    }
}
