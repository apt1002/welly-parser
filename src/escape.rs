use super::{Location, Token, UndoIterator, Parse};

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
        _input: &mut UndoIterator<I>,
    ) -> Option<Token<AST>> {
        todo!()
    }
}

impl Parse for Parser {
    type Input = char;
    type Output = AST;

    fn parse<
        I: Iterator<Item=Token<Self::Input>>,
    >(&self, input: &mut UndoIterator<I>) -> Option<Token<Self::Output>> {
        let start = match input.next() {
            Some(Token(loc, Ok('\\'))) => loc,
            other => { return other.map(Token::into); },
        };
        // We've read a backslash.
        input.next().and_then(|token| match token {
            Token(loc, Ok('0')) => {
                Some(Token::compound([start, loc], '\0'))
            },
            Token(loc, Ok('x')) => {
                self.backslash_x(start, loc, input)
            },
            Token(_, Ok(_)) => {
                input.undo(token);
                Some(Token::error([start], MISSING_SEQUENCE))
            },
            Token(loc, Err(e)) => {
                Some(Token(loc, Err(e)))
            },
        })
    }
}
