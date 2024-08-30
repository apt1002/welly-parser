use super::{Location, Token, TokenIterator};

/// A sequence of [`Token`]s enclosed in round brackets.
///
/// Note that this may include errors.
pub struct Round(Vec<Token>);

// ----------------------------------------------------------------------------

/// A parser that matches brackets.
pub struct Parser<I>(I);

impl<I: TokenIterator> Parser<I> {
    pub fn new(input: I) -> Self { Self(input) }

    /// Parses a [`Round`] representing the bracket starting at `open`,
    /// or [`None`] if [`self.input`] is exhausted first.
    fn parse_bracket(&mut self, open: Location) -> Option<Token> {
        let mut contents: Vec<Token> = Vec::new();
        while let Some(token) = self.next() {
            if let Token(close, Ok(token)) = &token {
                if let Some(&')') = token.downcast_ref::<char>() {
                    let loc = Location::union([open, *close]);
                    return Some(Token(loc, Ok(Box::new(Round(contents)))));
                }
            }
            contents.push(token);
        }
        None
    }
}

impl<I: TokenIterator> Iterator for Parser<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.0.next();
        if let Some(Token(open, Ok(token))) = &token {
            if let Some(&'(') = token.downcast_ref::<char>() {
                return self.parse_bracket(*open);
            }
        }
        token
    }
}
