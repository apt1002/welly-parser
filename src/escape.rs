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
        input: &mut Context<impl TokenIterator<T=char>>,
        num_digits: usize,
    ) -> Result<AST, Failure> {
        let mut ret = 0;
        for i in 0..num_digits {
            ret |= hex_digit_value(input.read()?).ok_or_else(
                || Failure::Error(MISSING_HEX.into())
            )? << (i * 4);
        }
        Ok(AST::Sequence(char::from_u32(ret).ok_or_else(
            || Failure::Error(INVALID.into())
        )?))
    }
}

impl Parse for Parser {
    type Input = char;
    type Output = AST;

    fn parse(&self, input: &mut Context<impl TokenIterator<T=char>>) -> Result<AST, Failure> {
        let c = input.read()?;
        if c != '\\' { return Ok(AST::Char(c)); }
        // We've read a backslash.
        match input.read()? {
            '0' => Ok(AST::Sequence('\0')),
            't' => Ok(AST::Sequence('\t')),
            'n' => Ok(AST::Sequence('\n')),
            'r' => Ok(AST::Sequence('\r')),
            '"' => Ok(AST::Sequence('"')),
            '\'' => Ok(AST::Sequence('\'')),
            '\\' => Ok(AST::Sequence('\\')),
            'x' => self.parse_hex(input, 2),
            'u' => self.parse_hex(input, 4),
            token => { input.unread(token); Err(Failure::Error(MISSING_SEQUENCE.into())) },
        }
    }
}
