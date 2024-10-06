use super::{Tree, EndOfFile, Location, Token, Stream};

pub const MISSING_OPEN: &'static str = "Unmatched close bracket";
pub const MISSING_CLOSE: &'static str = "Unmatched open bracket";

// ----------------------------------------------------------------------------

/// A sequence of [`Token`]s enclosed in round brackets.
#[derive(Debug)]
pub struct Round(pub Vec<Token>);

impl Tree for Round {}

/// A sequence of [`Token`]s enclosed in square brackets.
#[derive(Debug)]
pub struct Square(pub Vec<Token>);

impl Tree for Square {}

/// A sequence of [`Token`]s enclosed in round brackets.
#[derive(Debug)]
pub struct Brace(pub Vec<Token>);

impl Tree for Brace {}

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
    F: Fn(Vec<Token>) -> Box<dyn Tree>,
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

impl<I: Stream, F: Fn(Vec<Token>) -> Box<dyn Tree>> Stream for Parser<I, F> {
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
    use crate::{Characters};
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
                Characters::new("(a{b}(cd)){}", true)
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

    #[test]
    fn inside_out() {
        /// Pretend this is a parser for a complicated grammar.
        fn noop(parser: impl Stream) -> impl Stream { parser }

        /// Wrap 'parser' in a [`Round`] parser.
        fn round(parser: impl Stream) -> impl Stream {
            noop(Parser::new('(', ')', |contents| {
                let contents = noop(contents.into_iter()).read_all();
                Box::new(Round(contents))
            }, parser))
        }

        /// Wrap 'parser' in a [`Square`] parser.
        fn square(parser: impl Stream) -> impl Stream {
            round(Parser::new('[', ']', |contents| {
                let contents = round(contents.into_iter()).read_all();
                Box::new(Square(contents))
            }, parser))
        }

        /// Wrap 'parser' in a [`Brace`] parser.
        fn brace(parser: impl Stream) -> impl Stream {
            square(Parser::new('{', '}', |contents| {
                let contents = square(contents.into_iter()).read_all();
                Box::new(Brace(contents))
            }, parser))
        }

        let mut parser = brace(Characters::new("a{b[c(d(e[f{g}]))]}", true));
        assert_eq!(parser.read(), 'a');
        let mut contents1 = parser.read().unwrap::<Brace>().0.into_iter();
        assert_eq!(contents1.read(), 'b');
        let mut contents2 = contents1.read().unwrap::<Square>().0.into_iter();
        assert_eq!(contents2.read(), 'c');
        let mut contents3 = contents2.read().unwrap::<Round>().0.into_iter();
        assert_eq!(contents3.read(), 'd');
        let mut contents4 = contents3.read().unwrap::<Round>().0.into_iter();
        assert_eq!(contents4.read(), 'e');
        let mut contents5 = contents4.read().unwrap::<Square>().0.into_iter();
        assert_eq!(contents5.read(), 'f');
        let mut contents6 = contents5.read().unwrap::<Brace>().0.into_iter();
        assert_eq!(contents6.read(), 'g');
        assert_eq!(contents6.read(), EndOfFile);
        assert_eq!(contents5.read(), EndOfFile);
        assert_eq!(contents4.read(), EndOfFile);
        assert_eq!(contents3.read(), EndOfFile);
        assert_eq!(contents2.read(), EndOfFile);
        assert_eq!(contents1.read(), EndOfFile);
        assert_eq!(parser.read(), EndOfFile);
    }
}
