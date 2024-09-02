use std::any::{Any};
use super::{TokenIterator, Failure, fail, Context, Parse};

/// An escape sequence.
#[derive(Debug, PartialEq)]
pub struct Sequence(pub char);

pub const MISSING_SEQUENCE: &'static str = "Missing escape sequence";
pub const MISSING_HEX: &'static str = "Expected a hex digit";
pub const MISSING_OPEN_BRACE: &'static str = "Expected {";
pub const MISSING_HEX_OR_CLOSE_BRACE: &'static str = "Expected a hex digit or }";
pub const EXCESSIVE_HEX: &'static str = "Too many hex digits";
pub const INVALID: &'static str = "Invalid unicode scalar value";

fn hex_digit_value(c: char) -> Option<u32> {
    match c {
        '0'..='9' => Some((c as u32) - ('0' as u32)),
        'A'..='F' => Some((c as u32) - ('A' as u32) + 10),
        'a'..='f' => Some((c as u32) - ('a' as u32) + 10),
        _ => None,
    }
}

// ----------------------------------------------------------------------------

pub struct Parser;

impl Parser {
    fn parse_hex(
        &self,
        input: &mut Context<impl TokenIterator>,
        num_digits: usize,
    ) -> Result<Box<dyn Any>, Failure> {
        let mut ret: u32 = 0;
        for i in 0..num_digits {
            if let Some(c) = input.read::<char>()? {
                if let Some(d) = hex_digit_value(*c) {
                    ret |= d << (i * 4);
                } else {
                    input.unread(c);
                    return fail(MISSING_HEX);
                }
            } else {
                return fail(MISSING_HEX);
            }
        }
        if let Some(c) = char::from_u32(ret) {
            Ok(Box::new(Sequence(c)))
        } else {
            return fail(INVALID);
        }
    }
}

impl Parse for Parser {
    fn parse(&self, input: &mut Context<impl TokenIterator>) -> Result<Box<dyn Any>, Failure> {
        if let Some(c) = input.read::<char>()? {
            if *c != '\\' { return Ok(c); }
        } else {
            return input.read_any();
        }
        // We've read a backslash.
        if let Some(c) = input.read::<char>()? {
            match *c {
                '0' => { return Ok(Box::new(Sequence('\0'))) },
                't' => { return Ok(Box::new(Sequence('\t'))) },
                'n' => { return Ok(Box::new(Sequence('\n'))) },
                'r' => { return Ok(Box::new(Sequence('\r'))) },
                '"' => { return Ok(Box::new(Sequence('"'))) },
                '\'' => { return Ok(Box::new(Sequence('\''))) },
                '\\' => { return Ok(Box::new(Sequence('\\'))) },
                'x' => { return self.parse_hex(input, 2) },
                'u' => { return self.parse_hex(input, 4) },
                _ => { input.unread(c); },
            }
        }
        return fail(MISSING_SEQUENCE);
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::parser;
    use crate::buffer::{Characters};
    use super::*;

    #[test]
    fn some_characters() {
        let results: String = parser::Parser::new(
            Parser, Characters::new("abcdef")
        ).map(
            |t| *t.1.unwrap().downcast::<char>().unwrap()
        ).collect();
        assert_eq!(results, "abcdef");
    }

    #[test]
    fn some_escapes() {
        let mut results = parser::Parser::new(
            Parser, Characters::new("abcd\\nef")
        );
        assert_eq!(results.next().unwrap().downcast::<char>(), 'a');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'b');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'c');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'd');
        assert_eq!(results.next().unwrap().downcast::<Sequence>(), Sequence('\n'));
        assert_eq!(results.next().unwrap().downcast::<char>(), 'e');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'f');
        assert!(results.next().is_none());
    }

    #[test]
    fn bad_escape() {
        let mut results = parser::Parser::new(
            Parser, Characters::new("abcd\\ef")
        );
        assert_eq!(results.next().unwrap().downcast::<char>(), 'a');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'b');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'c');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'd');
        assert_eq!(results.next().unwrap().unwrap_err(), MISSING_SEQUENCE);
        assert_eq!(results.next().unwrap().downcast::<char>(), 'e');
        assert_eq!(results.next().unwrap().downcast::<char>(), 'f');
        assert!(results.next().is_none());
    }
}
