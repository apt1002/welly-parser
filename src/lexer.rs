use std::any::{Any};
use super::{escape, TokenIterator, Failure, fail, Context, Parse};

#[derive(Debug, Clone)]
pub struct Comment;

#[derive(Debug, Clone)]
pub struct CharacterLiteral(char);

#[derive(Debug, Clone)]
pub struct StringLiteral(String);

pub const UNTERMINATED_BLOCK_COMMENT: &'static str = "Unterminated block comment";
pub const UNTERMINATED_STRING: &'static str = "Unterminated string";
pub const MISSING_CHAR: &'static str = "Missing character literal";
pub const UNTERMINATED_CHAR: &'static str = "Unterminated character literal";
pub const BAD_ESCAPE: &'static str = "Unexpected escape sequence";

// ----------------------------------------------------------------------------

#[derive(Debug, Default)]
pub struct Parser;

impl Parser {
    /// Parse a line comment, starting after the initial `//`.
    fn parse_line_comment(
        &self, input:
        &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure> {
        loop {
            if let Some(c) = input.read::<char>()? {
                if *c == '\n' { input.unread(c); break; }
            } else if let Some(_) = input.read::<escape::Sequence>()? {
            } else {
                // E.g. end of file.
                break;
            }
        }
        Ok(Box::new(Comment))
    }

    /// Parse a line comment, starting after the initial `/*`.
    fn parse_block_comment(
        &self, input:
        &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure> {
        loop {
            if let Some(c) = input.read::<char>()? {
                if *c == '*' {
                    if let Some(c2) = input.read::<char>()? {
                        if *c2 == '/' { break; }
                        input.unread(c2);
                    }
                }
            } else if let Some(_) = input.read::<escape::Sequence>()? {
            } else {
                // E.g. end of file.
                return fail(UNTERMINATED_BLOCK_COMMENT);
            }
        }
        Ok(Box::new(Comment))
    }

    /// Parse a line comment, starting after the initial `'`.
    fn parse_character_literal(
        &self, input:
        &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure> {
        let c = if let Some(c) = input.read::<char>()? {
            if *c == '\'' { return fail(MISSING_CHAR); }
            *c
        } else if let Some(seq) = input.read::<escape::Sequence>()? {
            seq.0
        } else {
            return fail(MISSING_CHAR);
        };
        if let Some(c2) = input.read::<char>()? {
            if *c2 != '\'' { input.unread(c2); return fail(UNTERMINATED_CHAR); }
        } else {
            return fail(UNTERMINATED_CHAR);
        }
        Ok(Box::new(CharacterLiteral(c)))
    }

    /// Parse a line comment, starting after the initial `"`.
    fn parse_string_literal(
        &self, input:
        &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure> {
        let mut s = String::new();
        loop {
            let c = if let Some(c) = input.read::<char>()? {
                if *c == '"' { break; }
                *c
            } else if let Some(seq) = input.read::<escape::Sequence>()? {
                seq.0
            } else {
                return fail(UNTERMINATED_STRING);
            };
            s.push(c);
        }
        s.shrink_to_fit();
        Ok(Box::new(StringLiteral(s)))
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure> {
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
