// klujur-parser - Lexer for Klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Lexer (tokeniser) for Klujur source code.
//!
//! Converts a source string into a stream of tokens.

use std::fmt;
use std::iter::Peekable;
use std::str::Chars;

use num_bigint::BigInt;

/// A token produced by the lexer.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Delimiters
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    LBrace,   // {
    RBrace,   // }

    // Reader macros
    Quote,              // '
    SyntaxQuote,        // `
    Unquote,            // ~
    UnquoteSplice,      // ~@
    Deref,              // @
    VarQuote,           // #'
    AnonFn,             // #(
    Set,                // #{
    Discard,            // #_
    Regex,              // #" followed by string content
    Meta,               // ^
    ReaderCond,         // #?
    ReaderCondSplicing, // #?@

    // Literals
    Nil,
    True,
    False,
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Ratio(i64, i64),
    BigRatio(BigInt, BigInt),
    Char(char),
    String(String),
    Symbol(String),
    Keyword(String),

    // Special
    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Quote => write!(f, "'"),
            Token::SyntaxQuote => write!(f, "`"),
            Token::Unquote => write!(f, "~"),
            Token::UnquoteSplice => write!(f, "~@"),
            Token::Deref => write!(f, "@"),
            Token::VarQuote => write!(f, "#'"),
            Token::AnonFn => write!(f, "#("),
            Token::Set => write!(f, "#{{"),
            Token::Discard => write!(f, "#_"),
            Token::Regex => write!(f, "#\"...\""),
            Token::Meta => write!(f, "^"),
            Token::ReaderCond => write!(f, "#?"),
            Token::ReaderCondSplicing => write!(f, "#?@"),
            Token::Nil => write!(f, "nil"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Int(n) => write!(f, "{}", n),
            Token::BigInt(n) => write!(f, "{}N", n),
            Token::Float(n) => write!(f, "{}", n),
            Token::Ratio(num, den) => write!(f, "{}/{}", num, den),
            Token::BigRatio(num, den) => write!(f, "{}/{}N", num, den),
            Token::Char(c) => write!(f, "\\{}", c),
            Token::String(s) => write!(f, "\"{}\"", s),
            Token::Symbol(s) => write!(f, "{}", s),
            Token::Keyword(s) => write!(f, ":{}", s),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

/// Lexer error with position information.
#[derive(Debug, Clone)]
pub struct LexerError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Lexer error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for LexerError {}

/// The lexer converts source code into tokens.
pub struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
    line: usize,
    column: usize,
    /// Collected string for regex patterns (stored after reading #")
    regex_pattern: Option<String>,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given source code.
    pub fn new(source: &'a str) -> Self {
        Lexer {
            chars: source.chars().peekable(),
            line: 1,
            column: 1,
            regex_pattern: None,
        }
    }

    /// Get the next token from the source.
    pub fn next_token(&mut self) -> Result<Token, LexerError> {
        self.skip_whitespace_and_comments();

        let c = match self.peek() {
            Some(c) => c,
            None => return Ok(Token::Eof),
        };

        match c {
            // Delimiters
            '(' => {
                self.advance();
                Ok(Token::LParen)
            }
            ')' => {
                self.advance();
                Ok(Token::RParen)
            }
            '[' => {
                self.advance();
                Ok(Token::LBracket)
            }
            ']' => {
                self.advance();
                Ok(Token::RBracket)
            }
            '{' => {
                self.advance();
                Ok(Token::LBrace)
            }
            '}' => {
                self.advance();
                Ok(Token::RBrace)
            }

            // Reader macros
            '\'' => {
                self.advance();
                Ok(Token::Quote)
            }
            '`' => {
                self.advance();
                Ok(Token::SyntaxQuote)
            }
            '~' => {
                self.advance();
                if self.peek() == Some('@') {
                    self.advance();
                    Ok(Token::UnquoteSplice)
                } else {
                    Ok(Token::Unquote)
                }
            }
            '@' => {
                self.advance();
                Ok(Token::Deref)
            }
            '^' => {
                self.advance();
                Ok(Token::Meta)
            }

            // Dispatch macro (#)
            '#' => self.read_dispatch(),

            // String
            '"' => self.read_string(),

            // Character
            '\\' => self.read_char(),

            // Keyword
            ':' => self.read_keyword(),

            // Number or symbol starting with - or +
            '-' | '+' => self.read_number_or_symbol(),

            // Number
            '0'..='9' => self.read_number(),

            // Symbol
            _ if is_symbol_start(c) => self.read_symbol(),

            _ => Err(self.error(format!("Unexpected character: '{}'", c))),
        }
    }

    /// Collect all tokens into a vector.
    pub fn tokenize(&mut self) -> Result<Vec<Token>, LexerError> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token()?;
            if matches!(token, Token::Eof) {
                break;
            }
            tokens.push(token);
        }
        Ok(tokens)
    }

    /// Get the regex pattern if one was just read.
    pub fn take_regex_pattern(&mut self) -> Option<String> {
        self.regex_pattern.take()
    }

    /// Get the current line number (1-indexed).
    pub fn line(&self) -> usize {
        self.line
    }

    /// Get the current column number (1-indexed).
    pub fn column(&self) -> usize {
        self.column
    }

    // ========================================================================
    // Internal helpers
    // ========================================================================

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next();
        if let Some(ch) = c {
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        c
    }

    fn error(&self, message: String) -> LexerError {
        LexerError {
            message,
            line: self.line,
            column: self.column,
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() || c == ',' => {
                    self.advance();
                }
                Some(';') => {
                    // Skip to end of line
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.advance();
                    }
                }
                _ => break,
            }
        }
    }

    fn read_dispatch(&mut self) -> Result<Token, LexerError> {
        self.advance(); // consume #

        match self.peek() {
            Some('\'') => {
                self.advance();
                Ok(Token::VarQuote)
            }
            Some('(') => {
                self.advance();
                Ok(Token::AnonFn)
            }
            Some('{') => {
                self.advance();
                Ok(Token::Set)
            }
            Some('_') => {
                self.advance();
                Ok(Token::Discard)
            }
            Some('?') => {
                self.advance();
                // Check for splicing variant #?@
                if self.peek() == Some('@') {
                    self.advance();
                    Ok(Token::ReaderCondSplicing)
                } else {
                    Ok(Token::ReaderCond)
                }
            }
            Some('"') => {
                self.advance(); // consume "
                let pattern = self.read_regex_content()?;
                self.regex_pattern = Some(pattern);
                Ok(Token::Regex)
            }
            Some('#') => {
                // ##Inf, ##-Inf, ##NaN
                self.advance();
                self.read_special_float()
            }
            Some(c) if c.is_ascii_digit() => {
                // Anonymous function argument like %1, handled in symbol
                Err(self.error("Unexpected dispatch character after #".to_string()))
            }
            Some(c) => Err(self.error(format!("Unknown dispatch macro: #{}", c))),
            None => Err(self.error("Unexpected end of input after #".to_string())),
        }
    }

    fn read_special_float(&mut self) -> Result<Token, LexerError> {
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if is_symbol_char(c) {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        match name.as_str() {
            "Inf" => Ok(Token::Float(f64::INFINITY)),
            "-Inf" => Ok(Token::Float(f64::NEG_INFINITY)),
            "NaN" => Ok(Token::Float(f64::NAN)),
            _ => Err(self.error(format!("Unknown special value: ##{}", name))),
        }
    }

    fn read_string(&mut self) -> Result<Token, LexerError> {
        self.advance(); // consume opening "
        let content = self.read_string_content()?;
        Ok(Token::String(content))
    }

    fn read_string_content(&mut self) -> Result<String, LexerError> {
        let mut s = String::new();

        loop {
            match self.advance() {
                Some('"') => break,
                Some('\\') => match self.advance() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('r') => s.push('\r'),
                    Some('\\') => s.push('\\'),
                    Some('"') => s.push('"'),
                    Some('u') => {
                        let code = self.read_unicode_escape()?;
                        s.push(code);
                    }
                    Some(c) => return Err(self.error(format!("Unknown escape sequence: \\{}", c))),
                    None => return Err(self.error("Unterminated string escape".to_string())),
                },
                Some(c) => s.push(c),
                None => return Err(self.error("Unterminated string".to_string())),
            }
        }

        Ok(s)
    }

    /// Read regex pattern content - preserves backslashes for regex engine.
    /// Only \" is processed (to allow closing quote in pattern).
    fn read_regex_content(&mut self) -> Result<String, LexerError> {
        let mut s = String::new();

        loop {
            match self.advance() {
                Some('"') => break,
                Some('\\') => {
                    // Only process \" to allow embedded quotes; pass all other escapes through
                    match self.peek() {
                        Some('"') => {
                            self.advance();
                            s.push('"');
                        }
                        Some('\\') => {
                            // Preserve double backslash for regex engine
                            self.advance();
                            s.push_str("\\\\");
                        }
                        _ => {
                            // Pass the backslash through as-is for regex engine
                            s.push('\\');
                        }
                    }
                }
                Some(c) => s.push(c),
                None => return Err(self.error("Unterminated regex pattern".to_string())),
            }
        }

        Ok(s)
    }

    fn read_unicode_escape(&mut self) -> Result<char, LexerError> {
        let mut hex = String::with_capacity(4);
        for _ in 0..4 {
            match self.advance() {
                Some(c) if c.is_ascii_hexdigit() => hex.push(c),
                Some(c) => {
                    return Err(self.error(format!("Invalid hex digit in unicode escape: {}", c)));
                }
                None => return Err(self.error("Unterminated unicode escape".to_string())),
            }
        }
        let code = u32::from_str_radix(&hex, 16)
            .map_err(|_| self.error("Invalid unicode escape".to_string()))?;
        char::from_u32(code)
            .ok_or_else(|| self.error(format!("Invalid unicode code point: {}", code)))
    }

    fn read_char(&mut self) -> Result<Token, LexerError> {
        self.advance(); // consume backslash

        // Read the character or character name
        let first = self
            .advance()
            .ok_or_else(|| self.error("Expected character after \\".to_string()))?;

        // Check for named characters or unicode escape
        if first.is_ascii_alphabetic() {
            let mut name = String::new();
            name.push(first);

            // Peek ahead to see if this is a named character
            while let Some(c) = self.peek() {
                if c.is_ascii_alphanumeric() {
                    name.push(c);
                    self.advance();
                } else {
                    break;
                }
            }

            // Check for named characters
            match name.as_str() {
                "newline" => Ok(Token::Char('\n')),
                "space" => Ok(Token::Char(' ')),
                "tab" => Ok(Token::Char('\t')),
                "return" => Ok(Token::Char('\r')),
                "backspace" => Ok(Token::Char('\x08')),
                "formfeed" => Ok(Token::Char('\x0C')),
                s if s.len() == 1 => Ok(Token::Char(s.chars().next().unwrap())),
                s if s.starts_with('u') && s.len() == 5 => {
                    // Unicode escape like \u03BB
                    let hex = &s[1..];
                    let code = u32::from_str_radix(hex, 16)
                        .map_err(|_| self.error(format!("Invalid unicode escape: \\{}", s)))?;
                    let ch = char::from_u32(code).ok_or_else(|| {
                        self.error(format!("Invalid unicode code point: {}", code))
                    })?;
                    Ok(Token::Char(ch))
                }
                _ => Err(self.error(format!("Unknown character name: \\{}", name))),
            }
        } else {
            Ok(Token::Char(first))
        }
    }

    fn read_keyword(&mut self) -> Result<Token, LexerError> {
        self.advance(); // consume :

        // Check for auto-resolved keyword (::)
        let auto_resolve = if self.peek() == Some(':') {
            self.advance();
            true
        } else {
            false
        };

        let mut name = String::new();
        if auto_resolve {
            name.push_str("::");
        }

        while let Some(c) = self.peek() {
            if is_symbol_char(c) || c == '/' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() && !auto_resolve {
            return Err(self.error("Expected keyword name after :".to_string()));
        }

        Ok(Token::Keyword(name))
    }

    fn read_symbol(&mut self) -> Result<Token, LexerError> {
        let mut name = String::new();

        while let Some(c) = self.peek() {
            if is_symbol_char(c) || c == '/' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Check for reserved words
        match name.as_str() {
            "nil" => Ok(Token::Nil),
            "true" => Ok(Token::True),
            "false" => Ok(Token::False),
            _ => Ok(Token::Symbol(name)),
        }
    }

    fn read_number_or_symbol(&mut self) -> Result<Token, LexerError> {
        let sign = self.advance().unwrap(); // + or -

        match self.peek() {
            Some(c) if c.is_ascii_digit() => {
                // It's a number
                let mut s = String::new();
                s.push(sign);
                self.collect_number_chars(&mut s);
                self.parse_number(&s)
            }
            Some(c) if is_symbol_char(c) => {
                // It's a symbol like +foo or ->>
                let mut name = String::new();
                name.push(sign);
                while let Some(c) = self.peek() {
                    if is_symbol_char(c) || c == '/' {
                        name.push(c);
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(Token::Symbol(name))
            }
            _ => {
                // Just + or - as a symbol
                Ok(Token::Symbol(sign.to_string()))
            }
        }
    }

    fn read_number(&mut self) -> Result<Token, LexerError> {
        let mut s = String::new();
        self.collect_number_chars(&mut s);
        self.parse_number(&s)
    }

    fn collect_number_chars(&mut self, s: &mut String) {
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric()
                || c == '.'
                || c == '/'
                || c == '+'
                || c == '-'
                || c == 'e'
                || c == 'E'
                || c == 'x'
                || c == 'X'
                || c == 'r'
            {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
    }

    fn parse_number(&self, s: &str) -> Result<Token, LexerError> {
        // Check for ratio
        if let Some(slash_pos) = s.find('/')
            && !s.starts_with("0x")
            && !s.starts_with("0X")
            && !s.contains('r')
        {
            let num_str = &s[..slash_pos];
            let den_str = &s[slash_pos + 1..];

            // Try parsing as i64 first, fall back to BigInt on overflow
            match (num_str.parse::<i64>(), den_str.parse::<i64>()) {
                (Ok(num), Ok(den)) => {
                    if den == 0 {
                        return Err(self.error("Division by zero in ratio".to_string()));
                    }
                    return Ok(Token::Ratio(num, den));
                }
                _ => {
                    // Overflow - use BigInt
                    let num: BigInt = num_str
                        .parse()
                        .map_err(|_| self.error(format!("Invalid numerator: {}", num_str)))?;
                    let den: BigInt = den_str
                        .parse()
                        .map_err(|_| self.error(format!("Invalid denominator: {}", den_str)))?;
                    if den == BigInt::from(0) {
                        return Err(self.error("Division by zero in ratio".to_string()));
                    }
                    return Ok(Token::BigRatio(num, den));
                }
            }
        }

        // Check for float (contains . or e/E without radix prefix)
        if (s.contains('.') || s.contains('e') || s.contains('E'))
            && !s.contains('r')
            && !s.starts_with("0x")
            && !s.starts_with("0X")
        {
            let n: f64 = s
                .parse()
                .map_err(|_| self.error(format!("Invalid float: {}", s)))?;
            return Ok(Token::Float(n));
        }

        // Integer with potential base prefix - returns Int or BigInt
        self.parse_int(s)
    }

    fn parse_int(&self, s: &str) -> Result<Token, LexerError> {
        use num_traits::Num;

        // Store original string for special cases like i64::MIN
        let original = s;

        let (is_negative, s) = if let Some(rest) = s.strip_prefix('-') {
            (true, rest)
        } else if let Some(rest) = s.strip_prefix('+') {
            (false, rest)
        } else {
            (false, s)
        };

        // Check for explicit BigInt suffix (N)
        let (force_bigint, s) = if let Some(rest) = s.strip_suffix('N') {
            (true, rest)
        } else {
            (false, s)
        };

        // Determine base and digits
        let (base, digits) = if s.starts_with("0x") || s.starts_with("0X") {
            (16, &s[2..])
        } else if s.starts_with('0') && s.len() > 1 && !s.contains('r') {
            (8, &s[1..])
        } else if let Some(r_pos) = s.find('r') {
            let radix: u32 = s[..r_pos]
                .parse()
                .map_err(|_| self.error(format!("Invalid radix: {}", &s[..r_pos])))?;
            if !(2..=36).contains(&radix) {
                return Err(self.error(format!("Radix must be between 2 and 36: {}", radix)));
            }
            (radix, &s[r_pos + 1..])
        } else {
            (10, s)
        };

        // If explicit N suffix, always parse as BigInt
        if force_bigint {
            let big = BigInt::from_str_radix(digits, base)
                .map_err(|_| self.error(format!("Invalid BigInt: {}N", s)))?;
            let big = if is_negative { -big } else { big };
            return Ok(Token::BigInt(big));
        }

        // For base 10, try parsing the full signed string first to handle i64::MIN correctly.
        // i64::MIN's magnitude (9223372036854775808) exceeds i64::MAX (9223372036854775807),
        // so parsing just the digits would fail even though -9223372036854775808 fits in i64.
        if base == 10
            && let Ok(n) = original.parse::<i64>()
        {
            return Ok(Token::Int(n));
        }

        // Try parsing as i64 first
        match i64::from_str_radix(digits, base) {
            Ok(n) => {
                let result = if is_negative {
                    n.checked_neg().ok_or_else(|| {
                        // Overflow on negation - promote to BigInt
                        self.error(String::new())
                    })
                } else {
                    Ok(n)
                };
                match result {
                    Ok(n) => Ok(Token::Int(n)),
                    Err(_) => {
                        // Overflow - promote to BigInt
                        let big = BigInt::from_str_radix(digits, base)
                            .map_err(|_| self.error(format!("Invalid integer: {}", s)))?;
                        let big = if is_negative { -big } else { big };
                        Ok(Token::BigInt(big))
                    }
                }
            }
            Err(_) => {
                // Overflow or invalid - try BigInt
                match BigInt::from_str_radix(digits, base) {
                    Ok(big) => {
                        let big = if is_negative { -big } else { big };
                        Ok(Token::BigInt(big))
                    }
                    Err(_) => Err(self.error(format!("Invalid integer: {}", s))),
                }
            }
        }
    }
}

/// Check if a character can start a symbol.
fn is_symbol_start(c: char) -> bool {
    c.is_alphabetic()
        || matches!(
            c,
            '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | '<' | '=' | '>' | '?' | '_'
        )
}

/// Check if a character can appear in a symbol.
fn is_symbol_char(c: char) -> bool {
    is_symbol_start(c) || c.is_ascii_digit() || c == '\'' || c == '#'
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str) -> Result<Vec<Token>, LexerError> {
        Lexer::new(s).tokenize()
    }

    #[test]
    fn test_delimiters() {
        assert_eq!(
            tokenize("()[]{}").unwrap(),
            vec![
                Token::LParen,
                Token::RParen,
                Token::LBracket,
                Token::RBracket,
                Token::LBrace,
                Token::RBrace,
            ]
        );
    }

    #[test]
    fn test_reader_macros() {
        assert_eq!(
            tokenize("' ` ~ ~@ @").unwrap(),
            vec![
                Token::Quote,
                Token::SyntaxQuote,
                Token::Unquote,
                Token::UnquoteSplice,
                Token::Deref,
            ]
        );
    }

    #[test]
    fn test_dispatch_macros() {
        assert_eq!(
            tokenize("#' #( #{  #_").unwrap(),
            vec![Token::VarQuote, Token::AnonFn, Token::Set, Token::Discard,]
        );
    }

    #[test]
    fn test_reader_cond_tokens() {
        assert_eq!(
            tokenize("#? #?@").unwrap(),
            vec![Token::ReaderCond, Token::ReaderCondSplicing,]
        );
    }

    #[test]
    fn test_nil_and_booleans() {
        assert_eq!(
            tokenize("nil true false").unwrap(),
            vec![Token::Nil, Token::True, Token::False,]
        );
    }

    #[test]
    fn test_integers() {
        assert_eq!(
            tokenize("0 1 42 -1 +5").unwrap(),
            vec![
                Token::Int(0),
                Token::Int(1),
                Token::Int(42),
                Token::Int(-1),
                Token::Int(5),
            ]
        );
    }

    #[test]
    fn test_hex_integers() {
        assert_eq!(
            tokenize("0x10 0xff 0xFF").unwrap(),
            vec![Token::Int(16), Token::Int(255), Token::Int(255),]
        );
    }

    #[test]
    fn test_octal_integers() {
        assert_eq!(
            tokenize("010 077").unwrap(),
            vec![Token::Int(8), Token::Int(63),]
        );
    }

    #[test]
    fn test_radix_integers() {
        assert_eq!(
            tokenize("2r1010 8r77 16rff 36rz").unwrap(),
            vec![
                Token::Int(10),
                Token::Int(63),
                Token::Int(255),
                Token::Int(35),
            ]
        );
    }

    #[test]
    fn test_bigint_literals() {
        // Explicit N suffix forces BigInt even for small numbers
        assert_eq!(
            tokenize("0N 42N -100N").unwrap(),
            vec![
                Token::BigInt(BigInt::from(0)),
                Token::BigInt(BigInt::from(42)),
                Token::BigInt(BigInt::from(-100)),
            ]
        );

        // Large numbers with N suffix
        let tokens = tokenize("18446744073709551614N").unwrap();
        assert_eq!(tokens.len(), 1);
        assert!(matches!(&tokens[0], Token::BigInt(n) if n.to_string() == "18446744073709551614"));

        // Hex with N suffix
        assert_eq!(
            tokenize("0xFFN").unwrap(),
            vec![Token::BigInt(BigInt::from(255))]
        );

        // Radix with N suffix
        assert_eq!(
            tokenize("2r1010N").unwrap(),
            vec![Token::BigInt(BigInt::from(10))]
        );
    }

    #[test]
    fn test_floats() {
        assert_eq!(
            tokenize("0.0 3.14 -2.5 1e10 1.5e-3").unwrap(),
            vec![
                Token::Float(0.0),
                Token::Float(3.14),
                Token::Float(-2.5),
                Token::Float(1e10),
                Token::Float(1.5e-3),
            ]
        );
    }

    #[test]
    fn test_ratios() {
        assert_eq!(
            tokenize("1/2 3/4 -1/3").unwrap(),
            vec![Token::Ratio(1, 2), Token::Ratio(3, 4), Token::Ratio(-1, 3),]
        );
    }

    #[test]
    fn test_special_floats() {
        let tokens = tokenize("##Inf ##-Inf ##NaN").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[0], Token::Float(f) if f == f64::INFINITY));
        assert!(matches!(tokens[1], Token::Float(f) if f == f64::NEG_INFINITY));
        assert!(matches!(tokens[2], Token::Float(f) if f.is_nan()));
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            tokenize(r#""""#).unwrap(),
            vec![Token::String("".to_string())]
        );
        assert_eq!(
            tokenize(r#""hello""#).unwrap(),
            vec![Token::String("hello".to_string())]
        );
        assert_eq!(
            tokenize(r#""hello\nworld""#).unwrap(),
            vec![Token::String("hello\nworld".to_string())]
        );
        assert_eq!(
            tokenize(r#""tab\there""#).unwrap(),
            vec![Token::String("tab\there".to_string())]
        );
    }

    #[test]
    fn test_chars() {
        assert_eq!(
            tokenize(r"\a \z \0").unwrap(),
            vec![Token::Char('a'), Token::Char('z'), Token::Char('0'),]
        );
    }

    #[test]
    fn test_named_chars() {
        assert_eq!(
            tokenize(r"\newline \space \tab").unwrap(),
            vec![Token::Char('\n'), Token::Char(' '), Token::Char('\t'),]
        );
    }

    #[test]
    fn test_unicode_chars() {
        assert_eq!(
            tokenize(r"\u0041 \u03BB").unwrap(),
            vec![Token::Char('A'), Token::Char('λ'),]
        );
    }

    #[test]
    fn test_symbols() {
        assert_eq!(
            tokenize("foo bar my-symbol").unwrap(),
            vec![
                Token::Symbol("foo".to_string()),
                Token::Symbol("bar".to_string()),
                Token::Symbol("my-symbol".to_string()),
            ]
        );
    }

    #[test]
    fn test_special_symbols() {
        assert_eq!(
            tokenize("+ - * / < > = !=").unwrap(),
            vec![
                Token::Symbol("+".to_string()),
                Token::Symbol("-".to_string()),
                Token::Symbol("*".to_string()),
                Token::Symbol("/".to_string()),
                Token::Symbol("<".to_string()),
                Token::Symbol(">".to_string()),
                Token::Symbol("=".to_string()),
                Token::Symbol("!=".to_string()),
            ]
        );
    }

    #[test]
    fn test_namespaced_symbols() {
        assert_eq!(
            tokenize("user/foo clojure.core/map").unwrap(),
            vec![
                Token::Symbol("user/foo".to_string()),
                Token::Symbol("clojure.core/map".to_string()),
            ]
        );
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            tokenize(":foo :bar :my-key").unwrap(),
            vec![
                Token::Keyword("foo".to_string()),
                Token::Keyword("bar".to_string()),
                Token::Keyword("my-key".to_string()),
            ]
        );
    }

    #[test]
    fn test_namespaced_keywords() {
        assert_eq!(
            tokenize(":user/foo").unwrap(),
            vec![Token::Keyword("user/foo".to_string()),]
        );
    }

    #[test]
    fn test_auto_resolved_keywords() {
        assert_eq!(
            tokenize("::foo").unwrap(),
            vec![Token::Keyword("::foo".to_string()),]
        );
    }

    #[test]
    fn test_whitespace() {
        assert_eq!(
            tokenize("  1   2   3  ").unwrap(),
            vec![Token::Int(1), Token::Int(2), Token::Int(3),]
        );
    }

    #[test]
    fn test_commas_as_whitespace() {
        assert_eq!(
            tokenize("[1, 2, 3]").unwrap(),
            vec![
                Token::LBracket,
                Token::Int(1),
                Token::Int(2),
                Token::Int(3),
                Token::RBracket,
            ]
        );
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            tokenize("1 ; comment\n2").unwrap(),
            vec![Token::Int(1), Token::Int(2),]
        );
    }

    #[test]
    fn test_regex() {
        let mut lexer = Lexer::new(r#"#"pattern""#);
        let token = lexer.next_token().unwrap();
        assert_eq!(token, Token::Regex);
        assert_eq!(lexer.take_regex_pattern(), Some("pattern".to_string()));
    }

    #[test]
    fn test_complex_expression() {
        let tokens = tokenize("(defn foo [x] (+ x 1))").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LParen,
                Token::Symbol("defn".to_string()),
                Token::Symbol("foo".to_string()),
                Token::LBracket,
                Token::Symbol("x".to_string()),
                Token::RBracket,
                Token::LParen,
                Token::Symbol("+".to_string()),
                Token::Symbol("x".to_string()),
                Token::Int(1),
                Token::RParen,
                Token::RParen,
            ]
        );
    }
}
