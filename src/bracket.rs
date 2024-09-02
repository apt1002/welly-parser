use std::any::{Any};

use super::{EndOfFile, Location, Token, TokenIterator};

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
    I: TokenIterator,
    F: Fn(Vec<Token>) -> Box<dyn Any>,
> Parser<I, F> {
    /// Construct a `bracket::Parser`.
    /// - input - the [`TokenIterator`] from which to read and parse input.
    /// - open - the [`char`] used to open a bracket.
    /// - close - the [`char`] used to close a bracket.
    /// - new_bracket - turns bracket contents into a bracket value.
    pub fn new(open: char, close: char, new_bracket: F, input: I) -> Self {
        Self {open, close, new_bracket, input, depth: 0}
    }

    /// Parses a bracket representing the bracket starting at `open`,
    /// or [`None`] if [`self.input`] is exhausted first.
    fn parse_bracket(&mut self, open_loc: Location) -> Option<Token> {
        let mut contents: Vec<Token> = Vec::new();
        while let Some(token) = self.next() {
            if let Token(close_loc, Ok(token)) = &token {
                if token.downcast_ref::<EndOfFile>().is_some() {
                    return Some(Token(open_loc, Err(MISSING_CLOSE.into())));
                }
                if let Some(c) = token.downcast_ref::<char>() {
                    if *c == self.close {
                        let loc = Location::union([open_loc, *close_loc]);
                        let bracket = (&self.new_bracket)(contents);
                        return Some(Token(loc, Ok(bracket)));
                    }
                }
            }
            contents.push(token);
        }
        None
    }
}

impl<I: TokenIterator, F: Fn(Vec<Token>) -> Box<dyn Any>> Iterator for Parser<I, F> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.input.next();
        if let Some(Token(loc, Ok(token))) = &token {
            if let Some(c) = token.downcast_ref::<char>() {
                if *c == self.open {
                    self.depth += 1;
                    return self.parse_bracket(*loc);
                }
                if *c == self.close {
                    if self.depth == 0 {
                        return Some(Token(*loc, Err(MISSING_OPEN.into())));
                    }
                    self.depth -= 1;
                }
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
        let mut contents1 = parser.next().unwrap().downcast::<Round>().0.into_iter();
        assert_eq!(contents1.next().unwrap().downcast::<char>(), 'a');
        let mut contents2 = contents1.next().unwrap().downcast::<Brace>().0.into_iter();
        assert_eq!(contents2.next().unwrap().downcast::<char>(), 'b');
        assert!(contents2.next().is_none());
        let mut contents2 = contents1.next().unwrap().downcast::<Round>().0.into_iter();
        assert_eq!(contents2.next().unwrap().downcast::<char>(), 'c');
        assert_eq!(contents2.next().unwrap().downcast::<char>(), 'd');
        assert!(contents2.next().is_none());
        assert!(contents1.next().is_none());
        let mut contents1 = parser.next().unwrap().downcast::<Brace>().0.into_iter();
        assert!(contents1.next().is_none());
        assert!(parser.next().is_none());
    }
}
