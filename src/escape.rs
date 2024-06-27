use super::{TokenIterator, Failure, Context, Parse};

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
    fn backslash_x(&self, _input: &mut Context<impl TokenIterator<T=char>>) -> Result<AST, Failure> {
        todo!()
    }
}

impl Parse for Parser {
    type Input = char;
    type Output = AST;

    fn parse(&self, input: &mut Context<impl TokenIterator<T=char>>) -> Result<AST, Failure> {
        let start = input.read()?;
        if start != '\\' { return Ok(start.into()); }
        // We've read a backslash.
        match input.read()? {
            '0' => Ok(AST::Sequence('\0')),
            'x' => self.backslash_x(input),
            token => { input.unread(token); Err(Failure::Error(MISSING_SEQUENCE.into())) },
        }
    }
}
