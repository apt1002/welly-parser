use std::any::{Any};

use super::{EndOfFile, Location, Token, Stream};

pub const MISSING_OPEN: &'static str = "Unmatched close bracket";
pub const MISSING_CLOSE: &'static str = "Unmatched open bracket";

// ----------------------------------------------------------------------------

/// A sequence of [`Token`]s enclosed in round brackets.
#[derive(Debug)]
pub struct Round(Vec<Token>);

/// A sequence of [`Token`]s enclosed in square brackets.
#[derive(Debug)]
pub struct Square(Vec<Token>);

/// A sequence of [`Token`]s enclosed in round brackets.
#[derive(Debug)]
pub struct Brace(Vec<Token>);

// ----------------------------------------------------------------------------

/// A parser that matches brackets.
pub struct Parser<I, F> {
    open: char,
    close: char,
    new_bracket: F,
    input: I,
    depth: usize
}

impl<
    I: Stream,
    F: Fn(Vec<Token>) -> Box<dyn Any>,
> Parser<I, F> {
    /// Construct a `bracket::Parser`.
    /// - input - the [`Stream`] from which to read and parse input.
    /// - open - the [`char`] used to open a bracket.
    /// - close - the [`char`] used to close a bracket.
    /// - new_bracket - turns bracket contents into a bracket value.
    pub fn new(open: char, close: char, new_bracket: F, input: I) -> Self {
        Self {open, close, new_bracket, input, depth: 0}
    }

    /// Parses a bracket representing the bracket starting at `open`,
    /// or [`None`] if [`self.input`] is exhausted first.
    fn parse_bracket(&mut self, open_loc: Location) -> Token {
        let mut contents: Vec<Token> = Vec::new();
        loop {
            let token = self.read();
            if token.is_incomplete() { return token; }
            if token == EndOfFile { return Token(open_loc, Err(MISSING_CLOSE.into())); }
            if token == self.close {
                let loc = Location::union([open_loc, token.0]);
                let bracket = (&self.new_bracket)(contents);
                return Token(loc, Ok(bracket));
            }
            contents.push(token);
        }
    }
}

impl<I: Stream, F: Fn(Vec<Token>) -> Box<dyn Any>> Stream for Parser<I, F> {
    fn read(&mut self) -> Token {
        let token = self.input.read();
        if let Some(c) = token.downcast_copy::<char>() {
            if c == self.open {
                self.depth += 1;
                return self.parse_bracket(token.0);
            }
            if c == self.close {
                if self.depth == 0 {
                    return Token(token.0, Err(MISSING_OPEN.into()));
                }
                self.depth -= 1;
            }
        }
        token
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::buffer::{Characters};
    use super::*;

    #[test]
    fn some_brackets() {
        let mut parser = Parser::new(
            '(',
            ')',
            |contents| Box::new(Round(contents)),
            Parser::new(
                '{',
                '}',
                |contents| Box::new(Brace(contents)),
                Characters::new("(a{b}(cd)){}")
            )
        );
        let mut contents1 = parser.read().unwrap::<Round>().0.into_iter();
        assert_eq!(contents1.read(), 'a');
        let mut contents2 = contents1.read().unwrap::<Brace>().0.into_iter();
        assert_eq!(contents2.read(), 'b');
        assert_eq!(contents2.read(), EndOfFile);
        let mut contents2 = contents1.read().unwrap::<Round>().0.into_iter();
        assert_eq!(contents2.read(), 'c');
        assert_eq!(contents2.read(), 'd');
        assert_eq!(contents2.read(), EndOfFile);
        assert_eq!(contents1.read(), EndOfFile);
        let mut contents1 = parser.read().unwrap::<Brace>().0.into_iter();
        assert_eq!(contents1.read(), EndOfFile);
        assert_eq!(parser.read(), EndOfFile);
    }
}
