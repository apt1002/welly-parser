use super::{Location, Token, TokenIterator, word};

#[derive(Debug, PartialEq)]
pub enum AST {
    Char(char),
    Comment(String),
    CharacterLiteral(char),
    StringLiteral(String),
    Whitespace(String),
    Symbol(String),
    Alphanumeric(String),
    Round(Vec<Token<AST>>),
}

impl From<word::AST> for AST {
    fn from(value: word::AST) -> Self {
        match value {
            word::AST::Char(c) => AST::Char(c),
            word::AST::Comment(s) => AST::Comment(s),
            word::AST::CharacterLiteral(c) => AST::CharacterLiteral(c),
            word::AST::StringLiteral(s) => AST::StringLiteral(s),
            word::AST::Whitespace(s) => AST::Whitespace(s),
            word::AST::Symbol(s) => AST::Symbol(s),
            word::AST::Alphanumeric(s) => AST::Alphanumeric(s),
        }
    }
}

// ----------------------------------------------------------------------------

/// A parser that matches brackets.
pub struct Parser<I>(I);

impl<I: TokenIterator<T=word::AST>> Parser<I> {
    pub fn new(input: I) -> Self { Self(input) }

    /// Parses an [`AST::Round`] representing the bracket starting at `open`,
    /// or [`None`] if [`self.input`] is exhausted first.
    fn parse_bracket(&mut self, open: Location) -> Option<Token<AST>> {
        let mut contents: Vec<Token<AST>> = Vec::new();
        loop {
            match self.next() {
                None => { return None; },
                Some(Token(close, Ok(AST::Char(')')))) => {
                    let loc = Location::union([open, close]);
                    return Some(Token(loc, Ok(AST::Round(contents))));
                },
                Some(t) => { contents.push(t); },
            }
        }
    }
}

impl<I: TokenIterator<T=word::AST>> Iterator for Parser<I> {
    type Item = Token<AST>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.next() {
            Some(Token(loc, Ok(word::AST::Char('(')))) => {
                return self.parse_bracket(loc);
            },
            t => t.map(|Token(loc, t)| Token(loc, t.map(AST::from))),
        }
    }
}

impl<I: TokenIterator<T=word::AST>> TokenIterator for Parser<I> {
    type T = AST;
}
