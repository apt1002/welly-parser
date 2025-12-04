//! Welly's lexer.

use std::collections::{HashMap};
use std::rc::{Rc};

use super::loc::{Location, Loc};
use super::stream::{Stream};
use super::enums::{BracketKind, Separator, Op, OpWord, ALL_OP_WORDS, ALL_ASSIGN_WORDS, ItemWord, ALL_ITEM_WORDS};

pub const UNTERMINATED_BLOCK_COMMENT: &'static str = "Unterminated block comment";
pub const UNTERMINATED_STRING: &'static str = "Unterminated string";
pub const MISSING_CHAR: &'static str = "Missing character literal";
pub const UNTERMINATED_CHAR: &'static str = "Unterminated character literal";
pub const BAD_ESCAPE: &'static str = "Unexpected escape sequence";
pub const MISSING_SEQUENCE: &'static str = "Missing escape sequence";
pub const MISSING_HEX: &'static str = "Expected a hex digit";
pub const ILLEGAL: &'static str = "Illegal character";
pub const INVALID: &'static str = "Invalid unicode scalar value";
pub const BAD_OPERATOR: &'static str = "Unknown operator";

/// If `c` is a hexadecimal digit, return its numeric value.
fn hex_digit_value(c: char) -> Option<u32> {
    match c {
        '0'..='9' => Some((c as u32) - ('0' as u32)),
        'A'..='F' => Some((c as u32) - ('A' as u32) + 10),
        'a'..='f' => Some((c as u32) - ('a' as u32) + 10),
        _ => None,
    }
}

// ----------------------------------------------------------------------------

/// A line comment or a block comment.
///
/// A line comment begins with `//` and ends before a newline.
/// A block comment begins with `/*` and ends with `*/`.
/// The text of the comment can only be retrieved if you know its [`Location`].
///
/// [`Location`]: super::Location
#[derive(Debug, Copy, Clone)]
pub struct Comment;

/// Lexer tokens that are complete expressions.
#[derive(Debug, Clone)]
pub enum Atom {
    /// A Welly character literal.
    ///
    /// A character literal consists of a single character or escape sequence
    /// enclosed in ASCII `'` characters.
    CharacterLiteral(char),

    /// A Welly string literal.
    ///
    /// A string literal consists of zero or more characters or escape sequences
    /// enclosed in ASCII `"` characters.
    StringLiteral(Rc<str>),

    /// A Welly identifier, tag or number: a maximal word made of letters,
    /// digits and underscores.
    Alphanumeric(Rc<str>),
}

/// The output type of the lexer.
#[derive(Debug, Clone)]
pub enum Lexeme {
    /*
    /// An indentation string: a maximal string of spaces starting at the
    /// beginning of a line.
    Indent(usize),
    */

    // A comment.
    Comment(Comment),

    /// Part of an expression.
    Atom(Atom),

    /// A keyword that introduces a statement.
    Item(ItemWord),

    /// A keyword that is an arithmetic operator or constant.
    Op(OpWord),

    /// A keyword that is an assignment operator.
    Assign(Option<Op>),

    /// A comma or semicolon.
    Separator(Separator),

    /// An open bracket character.
    Open(BracketKind),

    /// A close bracket character.
    Close(BracketKind),
}

// ----------------------------------------------------------------------------

pub type LexerError = &'static str;

/// Tests whether `c` can be part of a Welly operator keyword.
fn is_operator_char(c: char) -> bool {
    matches!(c, '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '^' | '|')
}

/// Tests whether `c` can be part of a Welly identifier or integer.
fn is_alphanumeric_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

///
pub struct Lexer {
    keywords: HashMap<&'static str, Lexeme>,
}

impl Default for Lexer {
    fn default() -> Self {
        let mut keywords = HashMap::new();
        for &(word, op) in &ALL_OP_WORDS {
            keywords.insert(word, Lexeme::Op(op));
        }
        for &(word, op) in &ALL_ASSIGN_WORDS {
            keywords.insert(word, Lexeme::Assign(op));
        }
        for &(word, item) in &ALL_ITEM_WORDS {
            keywords.insert(word, Lexeme::Item(item));
        }
        Self {keywords}
    }
}

impl Lexer {
    /// Parse a hexadecimal escape sequence, starting at the hexadecimal part.
    /// - escape - the [`Location`] of the backslash.
    /// - num_digits - the number of hexadecimal digits required.
    fn parse_hex(&self, escape: Location, input: &mut impl Stream<Item=Loc<char>>, num_digits: usize)
    -> Result<Loc<char>, Loc<LexerError>> {
        let mut ret: u32 = 0;
        let mut loc = escape;
        for i in 0..num_digits {
            let Some(c) = input.read() else { Err(Loc(MISSING_HEX, loc))? };
            if let Some(d) = hex_digit_value(c.0) {
                ret |= d << (i * 4);
                loc.end = c.1.end;
            } else {
                // `c` is not a digit.
                input.unread(c);
                Err(Loc(MISSING_HEX, loc))?
            }
        }
        let Some(ret) = char::from_u32(ret) else { Err(Loc(INVALID, loc))? };
        Ok(Loc(ret, loc))
    }

    /// Parse a single non-newline character or an escape sequence.
    /// Returns (if possible):
    /// - the `char` value.
    /// - `true` if it was escaped.
    /// Returns an error if there is an invalid escape sequence.
    fn parse_char(&self, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<(Loc<char>, bool)>, Loc<LexerError>> {
        let Some(c) = input.read() else { return Ok(None); };
        if c.0 == '\n' { input.unread(c); return Ok(None); }
        if c.0 != '\\' { return Ok(Some((c, false))); }
        let mut loc = c.1;
        // We've read a backslash.
        if let Some(c2) = input.read() {
            loc.end = c2.1.end;
            match c2.0 {
                '0' => { return Ok(Some((Loc('\0', loc), true))) },
                't' => { return Ok(Some((Loc('\t', loc), true))) },
                'n' => { return Ok(Some((Loc('\n', loc), true))) },
                'r' => { return Ok(Some((Loc('\r', loc), true))) },
                '"' => { return Ok(Some((Loc('"', loc), true))) },
                '\'' => { return Ok(Some((Loc('\'', loc), true))) },
                '\\' => { return Ok(Some((Loc('\\', loc), true))) },
                'x' => { return Ok(Some((self.parse_hex(loc, input, 2)?, true))) },
                'u' => { return Ok(Some((self.parse_hex(loc, input, 4)?, true))) },
                _ => { input.unread(c); loc = c.1; },
            }
        }
        Err(Loc(MISSING_SEQUENCE, loc))?
    }
    /// Parse a character literal, starting after the initial `'`.
    /// - quote - the [`Location`] of the initial `'`.
    fn parse_character_literal(&self, quote: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = quote;
        let Some((c, is_escaped)) = self.parse_char(input)? else { Err(Loc(MISSING_CHAR, loc))? };
        loc.end = c.1.end;
        if c.0 == '\'' && !is_escaped { Err(Loc(MISSING_CHAR, loc))? }
        let Some(c2) = input.read() else { Err(Loc(UNTERMINATED_CHAR, loc))? };
        if c2.0 != '\'' { input.unread(c2); Err(Loc(UNTERMINATED_CHAR, loc))? }
        loc.end = c2.1.end;
        Ok(Loc(Lexeme::Atom(Atom::CharacterLiteral(c.0)), loc))
    }

    /// Parse a string literal, starting after the initial `"`.
    /// - quote - the [`Location`] of the initial `"`.
    fn parse_string_literal(&self, quote: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = quote;
        let mut s = String::new();
        loop {
            let Some((c, is_escaped)) = self.parse_char(input)? else { Err(Loc(UNTERMINATED_STRING, loc))? };
            loc.end = c.1.end;
            if c.0 == '"' && !is_escaped { break; }
            s.push(c.0);
        }
        Ok(Loc(Lexeme::Atom(Atom::StringLiteral(s.into())), loc))
    }

    /// Parse a line comment, starting after the initial `//`.
    /// - slash - the [`Location`] of the initial `/`.
    fn parse_line_comment(&self, slash: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = slash;
        while let Some(c) = input.read() {
            if c.0 == '\n' { break; }
            loc.end = c.1.end;
        }
        Ok(Loc(Lexeme::Comment(Comment), loc))
    }

    /// Parse a line comment, starting after the initial `/*`.
    /// - slash - the [`Location`] of the initial `/`.
    fn parse_block_comment(&self, slash: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = slash;
        loop {
            let Some(c) = input.read() else {
                // E.g. `EndOfFile`.
                return Err(Some(Loc(UNTERMINATED_BLOCK_COMMENT, loc)));
            };
            if c.0 == '*' {
                if let Some(c2) = input.read() {
                    if c2.0 == '/' {
                        loc.end = c2.1.end;
                        return Ok(Loc(Lexeme::Comment(Comment), loc))
                    }
                    input.unread(c2);
                }
            }
            loc.end = c.1.end;
        }
    }

    /// Parse an operator keyword starting with `c`.
    fn parse_operator(&self, c: Loc<char>, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = c.1;
        let mut buffer = String::from(c.0);
        while let Some(c) = input.read() {
            if is_operator_char(c.0) {
                buffer.push(c.0);
                loc.end = c.1.end;
            } else {
                input.unread(c);
                break;
            }
        }
        if let Some(ret) = self.keywords.get(buffer.as_str()) {
            Ok(Loc(ret.clone(), loc))
        } else {
            Err(Some(Loc(BAD_OPERATOR, loc)))
        }
    }

    /// Parse an identifier or integer or alphabetic keyword starting with `c`.
    fn parse_alphanumeric(&self, c: Loc<char>, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Loc<Lexeme>, Option<Loc<LexerError>>> {
        let mut loc = c.1;
        let mut buffer = String::from(c.0);
        while let Some(c) = input.read() {
            if is_alphanumeric_char(c.0) {
                buffer.push(c.0);
                loc.end = c.1.end;
            } else {
                input.unread(c);
                break;
            }
        }
        if let Some(ret) = self.keywords.get(buffer.as_str()) {
            Ok(Loc(ret.clone(), loc))
        } else {
            Ok(Loc(Lexeme::Atom(Atom::Alphanumeric(buffer.into())), loc))
        }
    }

    /// Parse a [`Lexeme`].
    /// Returns:
    /// - Ok(None) - discard some input (e.g. whitespace).
    /// - Ok(Some(l)) - found a [`Lexeme`] `l`.
    /// - Err(None) - stream is empty.
    /// - Err(Some(e)) - found an error `e`.
    pub fn lex(&self, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let Some(c) = input.read() else { Err(None)? };
        Ok(Some(match c.0 {
            '\t' | '\n' | '\r' | ' ' => { return Ok(None); },
            '\'' => { self.parse_character_literal(c.1, input)? },
            '\"' => { self.parse_string_literal(c.1, input)? },
            ',' => { Loc(Lexeme::Separator(Separator::Comma), c.1) },
            ';' => { Loc(Lexeme::Separator(Separator::Semicolon), c.1) },
            '(' => { Loc(Lexeme::Open(BracketKind::Round), c.1) },
            ')' => { Loc(Lexeme::Close(BracketKind::Round), c.1) },
            '[' => { Loc(Lexeme::Open(BracketKind::Square), c.1) },
            ']' => { Loc(Lexeme::Close(BracketKind::Square), c.1) },
            '{' => { Loc(Lexeme::Open(BracketKind::Curly), c.1) },
            '}' => { Loc(Lexeme::Close(BracketKind::Curly), c.1) },
            '/' => {
                if let Some(c2) = input.read() {
                    match c2.0 {
                        '/' => { self.parse_line_comment(c2.1, input)? },
                        '*' => { self.parse_block_comment(c2.1, input)? },
                        _ => {
                            input.unread(c2);
                            self.parse_operator(c, input)?
                        },
                    }
                } else {
                    self.parse_operator(c, input)?
                }
            },
            _ => {
                if is_operator_char(c.0) { self.parse_operator(c, input)? }
                else if is_alphanumeric_char(c.0) { self.parse_alphanumeric(c, input)? }
                else { Err(Loc(ILLEGAL, c.1))? }
            },
        }))
    }
}

// ----------------------------------------------------------------------------

/* OLD version

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EndOfFile, Characters};

    #[test]
    fn line_comment() {
        let mut stream = Parser.parse_stream(Characters::new("a // b\nc", true));
        assert_eq!(stream.read(), 'a');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read(), Comment);
        assert_eq!(stream.read(), '\n');
        assert_eq!(stream.read(), 'c');
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn line_comment_eof() {
        let mut stream = Parser.parse_stream(Characters::new("a // b", true));
        assert_eq!(stream.read(), 'a');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read(), Comment);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn block_comment() {
        let mut stream = Parser.parse_stream(Characters::new("a /* b */", true));
        assert_eq!(stream.read(), 'a');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read(), Comment);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn block_comment_eof() {
        let mut stream = Parser.parse_stream(Characters::new("a /* b", true)); */
        assert_eq!(stream.read(), 'a');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read().unwrap_err(), UNTERMINATED_BLOCK_COMMENT);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn escapes() {
        let mut stream = Parser.parse_stream(Characters::new("f(\"h\\\"w\\\"!\", '\\n')", true));
        assert_eq!(stream.read(), 'f');
        assert_eq!(stream.read(), '(');
        assert_eq!(stream.read(), StringLiteral("h\"w\"!".into()));
        assert_eq!(stream.read(), ',');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read(), CharacterLiteral('\n'));
        assert_eq!(stream.read(), ')');
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn bad_newline() {
        let mut stream = Parser.parse_stream(Characters::new("'\n'", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_CHAR);
        assert_eq!(stream.read().unwrap_err(), MISSING_CHAR);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn bad_char() {
        let mut stream = Parser.parse_stream(Characters::new("'\\j'", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_SEQUENCE);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn bad_str() {
        let mut stream = Parser.parse_stream(Characters::new("\"a\\j\"", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_SEQUENCE);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn empty_char() {
        let mut stream = Parser.parse_stream(Characters::new("''", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_CHAR);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn double_char() {
        let mut stream = Parser.parse_stream(Characters::new("'ab'", true));
        assert_eq!(stream.read().unwrap_err(), UNTERMINATED_CHAR);
        assert_eq!(stream.read(), 'b');
        assert_eq!(stream.read().unwrap_err(), MISSING_CHAR);
        assert_eq!(stream.read(), EndOfFile);
    }
}
*/
