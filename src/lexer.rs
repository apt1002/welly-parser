//! Welly's lexer.

use super::{Tree, Stream, Context, Parse};

/// Represents a line comment or a block comment.
///
/// A line comment begins with `//` and ends before a newline.
/// A block comment begins with `/*` and ends with `*/`.
/// The text of the comment can only be retrieved if you know its [`Location`].
///
/// [`Location`]: super::Location
#[derive(Debug, Clone, PartialEq)]
pub struct Comment;

impl Tree for Comment {}

/// Represents a Welly character literal.
///
/// A character literal consists of a single character or escape sequence
/// enclosed in ASCII `'` characters.
#[derive(Debug, Clone, PartialEq)]
pub struct CharacterLiteral(pub char);

impl Tree for CharacterLiteral {}

/// Represents a Welly string literal.
///
/// A character literal consists of zero or more characters or escape sequences
/// enclosed in ASCII `"` characters.
#[derive(Debug, Clone, PartialEq)]
pub struct StringLiteral(pub String);

impl Tree for StringLiteral {}

pub const UNTERMINATED_BLOCK_COMMENT: &'static str = "Unterminated block comment";
pub const UNTERMINATED_STRING: &'static str = "Unterminated string";
pub const MISSING_CHAR: &'static str = "Missing character literal";
pub const UNTERMINATED_CHAR: &'static str = "Unterminated character literal";
pub const BAD_ESCAPE: &'static str = "Unexpected escape sequence";
pub const MISSING_SEQUENCE: &'static str = "Missing escape sequence";
pub const MISSING_HEX: &'static str = "Expected a hex digit";
pub const INVALID: &'static str = "Invalid unicode scalar value";

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

/// A [`Parse`] implementation that recognises [`Comment`]s,
/// [`CharacterLiteral`]s and [`StringLiteral`]s.
///
/// It parses a [`Stream`] that contains [`char`]s.
#[derive(Debug, Default)]
pub struct Parser;

impl Parser {
    /// Parse a line comment, starting after the initial `//`.
    fn parse_line_comment(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        while input.read_if::<char>(|&c| c != '\n')?.is_some() {}
        Ok(Box::new(Comment))
    }

    /// Parse a line comment, starting after the initial `/*`.
    fn parse_block_comment(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        loop {
            if let Some(c) = input.read::<char>()? {
                if *c == '*' {
                    if input.read_if::<char>(|&c| c == '/')?.is_some() { break; }
                }
            } else {
                // E.g. `EndOfFile`.
                Err(UNTERMINATED_BLOCK_COMMENT)?
            }
        }
        Ok(Box::new(Comment))
    }

    /// Parse `num_digits` hexadecimal digits.
    fn parse_hex(
        &self,
        input: &mut Context<impl Stream>,
        num_digits: usize,
    ) -> Result<char, String> {
        let mut ret: u32 = 0;
        for i in 0..num_digits {
            if let Some(c) = input.read::<char>()? {
                if let Some(d) = hex_digit_value(*c) {
                    ret |= d << (i * 4);
                } else {
                    // `c` is not a digit.
                    input.unread(c);
                    Err(MISSING_HEX)?
                }
            } else {
                // E.g. `EndOfFile`.
                Err(MISSING_HEX)?
            }
        }
        char::from_u32(ret).ok_or_else(|| INVALID.into())
    }

    /// Parse a single character or an escape sequence.
    /// - if_missing - the error message if we don't receive a character.
    /// Returns:
    /// - the `char` value.
    /// - `true` if it was escaped.
    fn parse_char(
        &self,
        input: &mut Context<impl Stream>,
        if_missing: &'static str,
    ) -> Result<(char, bool), String> {
        if let Some(c) = input.read::<char>()? {
            if *c != '\\' { return Ok((*c, false)); }
        } else {
            Err(if_missing)?
        }
        // We've read a backslash.
        if let Some(c) = input.read::<char>()? {
            match *c {
                '0' => { return Ok(('\0', true)) },
                't' => { return Ok(('\t', true)) },
                'n' => { return Ok(('\n', true)) },
                'r' => { return Ok(('\r', true)) },
                '"' => { return Ok(('"', true)) },
                '\'' => { return Ok(('\'', true)) },
                '\\' => { return Ok(('\\', true)) },
                'x' => { return Ok((self.parse_hex(input, 2)?, true)) },
                'u' => { return Ok((self.parse_hex(input, 4)?, true)) },
                _ => { input.unread(c); },
            }
        }
        Err(MISSING_SEQUENCE)?
        
    }

    /// Parse a character literal, starting after the initial `'`.
    fn parse_character_literal(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        let (c, is_escaped) = self.parse_char(input, MISSING_CHAR)?;
        if c == '\'' && !is_escaped { Err(MISSING_CHAR)? }
        if let Some(c2) = input.read::<char>()? {
            if *c2 != '\'' { input.unread(c2); Err(UNTERMINATED_CHAR)? }
        } else {
            Err(UNTERMINATED_CHAR)?
        }
        Ok(Box::new(CharacterLiteral(c)))
    }

    /// Parse a string literal, starting after the initial `"`.
    fn parse_string_literal(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        let mut s = String::new();
        loop {
            let (c, is_escaped) = self.parse_char(input, UNTERMINATED_STRING)?;
            if c == '"' && !is_escaped { break; }
            s.push(c);
        }
        s.shrink_to_fit();
        Ok(Box::new(StringLiteral(s)))
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        if let Some(c) = input.read::<char>()? {
            match *c {
                '/' => if let Some(c2) = input.read::<char>()? {
                    match *c2 {
                        '/' => { return self.parse_line_comment(input); },
                        '*' => { return self.parse_block_comment(input); },
                        _ => { input.unread(c2); },
                    }
                },
                '\'' => { return self.parse_character_literal(input); },
                '\"' => { return self.parse_string_literal(input); },
                _ => {},
            }
            Ok(c)
        } else {
            // E.g. end of file.
            input.read_any()
        }
    }
}

// ----------------------------------------------------------------------------

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
        let mut stream = Parser.parse_stream(Characters::new("a /* b", true));
        assert_eq!(stream.read(), 'a');
        assert_eq!(stream.read(), ' ');
        assert_eq!(stream.read().unwrap_err(), UNTERMINATED_BLOCK_COMMENT);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn escapes() {
        let mut stream = Parser.parse_stream(Characters::new("f(\"h\\\"w\\\"!\", '\n')", true));
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
    fn bad_char() {
        let mut stream = Parser.parse_stream(Characters::new("'\\j'", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_SEQUENCE);
        assert_eq!(stream.read(), 'j');
        assert_eq!(stream.read().unwrap_err(), MISSING_CHAR);
        assert_eq!(stream.read(), EndOfFile);
    }

    #[test]
    fn bad_str() {
        let mut stream = Parser.parse_stream(Characters::new("\"a\\j\"", true));
        assert_eq!(stream.read().unwrap_err(), MISSING_SEQUENCE);
        assert_eq!(stream.read(), 'j');
        assert_eq!(stream.read().unwrap_err(), UNTERMINATED_STRING);
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
