//! Welly's lexer.

use std::collections::{HashMap};
use std::{fmt};
use std::rc::{Rc};

use super::loc::{Location, Loc};
use super::stream::{Stream};
use super::enums::{BracketKind, Separator, Op, OpWord, ALL_OP_WORDS, ALL_ASSIGN_WORDS, ItemWord, ALL_ITEM_WORDS};

/// The error type of the `lex_xxx()` functions.
pub type LexerError = &'static str;

pub const UNTERMINATED_STR: LexerError = "Unterminated string";
pub const MISSING_CHAR: LexerError = "Missing character literal";
pub const UNTERMINATED_CHAR: LexerError = "Unterminated character literal";
pub const BAD_ESCAPE: LexerError = "Unexpected escape sequence";
pub const MISSING_SEQUENCE: LexerError = "Missing escape sequence";
pub const MISSING_HEX: LexerError = "Expected a hex digit";
pub const ILLEGAL: LexerError = "Illegal character";
pub const INVALID: LexerError = "Invalid unicode scalar value";
pub const BAD_OPERATOR: LexerError = "Unknown operator";

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
#[derive(Clone)]
pub enum Atom {
    /// A Welly character literal.
    ///
    /// A character literal consists of a single character or escape sequence
    /// enclosed in ASCII `'` characters.
    CharLiteral(char),

    /// A Welly string literal.
    ///
    /// A string literal consists of zero or more characters or escape sequences
    /// enclosed in ASCII `"` characters.
    StrLiteral(Rc<str>),

    /// A Welly identifier, tag or number: a maximal word made of letters,
    /// digits and underscores.
    Alphanumeric(Rc<str>),
}

impl fmt::Debug for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::CharLiteral(c) => c.fmt(f),
            Self::StrLiteral(s) => s.fmt(f),
            Self::Alphanumeric(s) => f.write_str(s),
        }
    }
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
    fn lex_hex(&self, escape: Location, input: &mut impl Stream<Item=Loc<char>>, num_digits: usize)
    -> Result<Loc<char>, Option<Loc<LexerError>>> {
        let mut ret: u32 = 0;
        let mut loc = escape;
        for i in 0..num_digits {
            let Some(c) = input.read() else { Err(None)? };
            loc.end = c.1.end;
            let Some(d) = hex_digit_value(c.0) else { Err(Loc(MISSING_HEX, loc))? };
            ret |= d << (i * 4);
        }
        let Some(ret) = char::from_u32(ret) else { Err(Loc(INVALID, loc))? };
        Ok(Loc(ret, loc))
    }

    /// Parse a single non-newline character or an escape sequence.
    /// Returns (if possible):
    /// - the `char` value.
    /// - `true` if it was escaped.
    /// Returns an error if there is an invalid escape sequence.
    fn lex_char(&self, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<(Loc<char>, bool)>, Option<Loc<LexerError>>> {
        let Some(c) = input.read() else { Err(None)? };
        if c.0 == '\n' { input.unread(c); return Ok(None); }
        if c.0 != '\\' { return Ok(Some((c, false))); }
        let mut loc = c.1;
        // We've read a backslash.
        let Some(c2) = input.read() else { Err(None)? };
        loc.end = c2.1.end;
        let ret: char = match c2.0 {
            '0' => '\0',
            't' => '\t',
            'n' => '\n',
            'r' => '\r',
            '"' => '"',
            '\'' => '\'',
            '\\' => '\\',
            'x' => { return Ok(Some((self.lex_hex(loc, input, 2)?, true))) },
            'u' => { return Ok(Some((self.lex_hex(loc, input, 4)?, true))) },
            _ => { Err(Loc(MISSING_SEQUENCE, loc))? },
        };
        Ok(Some((Loc(ret, loc), true)))
    }

    /// Parse a character literal, starting after the initial `'`.
    /// - quote - the [`Location`] of the initial `'`.
    fn lex_char_literal(&self, quote: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = quote;
        let Some((c, is_escaped)) = self.lex_char(input)? else { Err(Loc(MISSING_CHAR, loc))? };
        loc.end = c.1.end;
        if c.0 == '\'' && !is_escaped { Err(Loc(MISSING_CHAR, loc))? }
        let Some(c2) = input.read() else { Err(None)? };
        loc.end = c2.1.end;
        if c2.0 != '\'' { Err(Loc(UNTERMINATED_CHAR, loc))? }
        Ok(Some(Loc(Lexeme::Atom(Atom::CharLiteral(c.0)), loc)))
    }

    /// Parse a string literal, starting after the initial `"`.
    /// - quote - the [`Location`] of the initial `"`.
    fn lex_str_literal(&self, quote: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = quote;
        let mut s = String::new();
        loop {
            let Some((c, is_escaped)) = self.lex_char(input)? else { Err(Loc(UNTERMINATED_STR, loc))? };
            loc.end = c.1.end;
            if c.0 == '"' && !is_escaped { break; }
            s.push(c.0);
        }
        Ok(Some(Loc(Lexeme::Atom(Atom::StrLiteral(s.into())), loc)))
    }

    /// Parse a line comment, starting after the initial `//`.
    /// - slash - the [`Location`] of the initial `/`.
    fn lex_line_comment(&self, slash: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = slash;
        loop {
            let Some(c) = input.read() else { Err(None)? };
            if c.0 == '\n' { break; }
            loc.end = c.1.end;
        }
        Ok(Some(Loc(Lexeme::Comment(Comment), loc)))
    }

    /// Parse a line comment, starting after the initial `/*`.
    /// - slash - the [`Location`] of the initial `/`.
    fn lex_block_comment(&self, slash: Location, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = slash;
        loop {
            let Some(c) = input.read() else { Err(None)? };
            if c.0 == '*' {
                let Some(c2) = input.read() else { Err(None)? };
                if c2.0 == '/' {
                    loc.end = c2.1.end;
                    break;
                }
                input.unread(c2);
            }
        }
        Ok(Some(Loc(Lexeme::Comment(Comment), loc)))
    }

    /// Parse an operator keyword starting with `c`.
    fn lex_operator(&self, c: Loc<char>, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = c.1;
        let mut buffer = String::from(c.0);
        loop {
            let Some(c) = input.read() else { Err(None)? };
            if is_operator_char(c.0) {
                buffer.push(c.0);
                loc.end = c.1.end;
            } else {
                input.unread(c);
                break;
            }
        }
        let ret = if let Some(ret) = self.keywords.get(buffer.as_str()) {
            ret.clone()
        } else {
            Err(Loc(BAD_OPERATOR, loc))?
        };
        Ok(Some(Loc(ret, loc)))
    }

    /// Parse an identifier or integer or alphabetic keyword starting with `c`.
    fn lex_alphanumeric(&self, c: Loc<char>, input: &mut impl Stream<Item=Loc<char>>)
    -> Result<Option<Loc<Lexeme>>, Option<Loc<LexerError>>> {
        let mut loc = c.1;
        let mut buffer = String::from(c.0);
        loop {
            let Some(c) = input.read() else { Err(None)? };
            if is_alphanumeric_char(c.0) {
                buffer.push(c.0);
                loc.end = c.1.end;
            } else {
                input.unread(c);
                break;
            }
        }
        let ret = if let Some(ret) = self.keywords.get(buffer.as_str()) {
            ret.clone()
        } else {
            Lexeme::Atom(Atom::Alphanumeric(buffer.into()))
        };
        Ok(Some(Loc(ret, loc)))
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
        let l: Lexeme = match c.0 {
            '\t' | '\n' | '\r' | ' ' => { return Ok(None); },
            '\'' => { return self.lex_char_literal(c.1, input); },
            '\"' => { return self.lex_str_literal(c.1, input); },
            ',' => Lexeme::Separator(Separator::Comma),
            ';' => Lexeme::Separator(Separator::Semicolon),
            '(' => Lexeme::Open(BracketKind::Round),
            ')' => Lexeme::Close(BracketKind::Round),
            '[' => Lexeme::Open(BracketKind::Square),
            ']' => Lexeme::Close(BracketKind::Square),
            '{' => Lexeme::Open(BracketKind::Curly),
            '}' => Lexeme::Close(BracketKind::Curly),
            '/' => {
                let Some(c2) = input.read() else { Err(None)? };
                match c2.0 {
                    '/' => { return self.lex_line_comment(c.1, input); },
                    '*' => { return self.lex_block_comment(c.1, input); },
                    _ => {
                        input.unread(c2);
                        return self.lex_operator(c, input);
                    },
                }
            },
            _ => {
                if is_operator_char(c.0) { return self.lex_operator(c, input); }
                else if is_alphanumeric_char(c.0) { return self.lex_alphanumeric(c, input); }
                else { Err(Loc(ILLEGAL, c.1))? }
            },
        };
        Ok(Some(Loc(l, c.1)))
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
