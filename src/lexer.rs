use super::{escape, TokenIterator, Failure, fail, Context, Parse};

#[derive(Debug, Clone, PartialEq)]
pub enum AST {
    Char(char),
    Comment(String),
    CharacterLiteral(char),
    StringLiteral(String),
}

pub const UNTERMINATED_BLOCK_COMMENT: &'static str = "Unterminated block comment";
pub const UNTERMINATED_STRING: &'static str = "Unterminated string";
pub const MISSING_CHAR: &'static str = "Missing character literal";
pub const UNTERMINATED_CHAR: &'static str = "Unterminated character literal";
pub const BAD_ESCAPE: &'static str = "Unexpected escape sequence";

// ----------------------------------------------------------------------------

#[derive(Debug, Default)]
pub struct Parser;

impl Parse for Parser {
    type Input = escape::AST;

    type Output = AST;

    fn parse(
        &self,
        input: &mut Context<impl TokenIterator<T=Self::Input>>,
    ) -> Result<Self::Output, Failure> {
        let c = match input.read()? {
            escape::AST::Sequence(_) => fail(BAD_ESCAPE)?,
            escape::AST::Char(c) => c,
        };
        match c {
            '/' => match input.read()? {
                escape::AST::Char('/') => {
                    // Line comment.
                    let mut s = String::new();
                    loop {
                        let c = input.read()?;
                        if c == escape::AST::Char('\n') { input.unread(c); break; }
                        s.push(c.to_char())
                    }
                    s.shrink_to_fit();
                    Ok(AST::Comment(s))
                },
                escape::AST::Char('*') => {
                    // Block comment.
                    let mut s = String::new();
                    loop {
                        let c = input.read()?;
                        if c == escape::AST::Char('*') {
                            let c2 = input.read()?;
                            if c2 == escape::AST::Char('/') { break; }
                            input.unread(c2);
                        }
                        s.push(c.to_char())
                    }
                    s.shrink_to_fit();
                    Ok(AST::Comment(s))
                },
                c2 => { input.unread(c2); Ok(AST::Char(c)) },
            },
            '\'' => {
                let c = input.read()?;
                if c == escape::AST::Char('\'') { fail(MISSING_CHAR)? }
                if input.read()? != escape::AST::Char('\'') { fail(UNTERMINATED_CHAR)? }
                Ok(AST::CharacterLiteral(c.to_char()))
            },
            '\"' => {
                let mut s = String::new();
                loop {
                    let c = input.read()?;
                    if c == escape::AST::Char('"') { break; }
                    s.push(c.to_char());
                }
                s.shrink_to_fit();
                Ok(AST::StringLiteral(s))
            },
            c => Ok(AST::Char(c)),
        }
    }
}
