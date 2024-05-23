use std::iter::{Peekable};
use super::{Location, Token, Parse};

pub enum AST {
    Char(char),
    Sequence(char),
}

impl From<char> for AST {
    fn from(value: char) -> Self { AST::Char(value) }
}

pub const MISSING_SEQUENCE: &'static str = "Missing escape sequence";
pub const MISSING_HEX: &'static str = "Expected a hex digit";
pub const MISSING_OPEN_BRACE: &'static str = "Expected {";
pub const MISSING_HEX_OR_CLOSE_BRACE: &'static str = "Expected a hex digit or }";
pub const EXCESSIVE_HEX: &'static str = "Too many hex digits";
pub const INVALID: &'static str = "Invalid unicode scalar value";

// ----------------------------------------------------------------------------

pub struct Parser;

impl Parser {
    fn backslash_x<I: Iterator<Item=Token<char>>>(
        &self,
        _start: Location,
        _loc_x: Location,
        _input: &mut Peekable<I>,
    ) -> Option<Token<AST>> {
        todo!()
    }
}

impl Parse for Parser {
    type Input = char;
    type Output = AST;

    fn parse<I: Iterator<Item=Token<Self::Input>>>(&self, input: &mut Peekable<I>) -> Option<Token<Self::Output>> {
        let start = match input.next() {
            Some(Token(loc, Ok('\\'))) => loc,
            other => { return other.map(Token::into); },
        };
        // We've read a backslash.
        match input.peek() {
            Some(&Token(loc, Ok('0'))) => {
                input.next();
                Some(Token::compound([start, loc], '\0'))
            },
            Some(&Token(loc, Ok('x'))) => {
                input.next();
                self.backslash_x(start, loc, input)
            },
            Some(&Token(_, Ok(_))) => Some(Token::error([start], MISSING_SEQUENCE)),
            Some(&Token(_, Err(_))) => {
                let Token(loc, e) = input.next().unwrap();
                Some(Token(loc, Err(e.unwrap_err())))
            },
            None => None,
        }
    }
}
