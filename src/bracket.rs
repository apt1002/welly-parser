//! Welly's bracket matcher.

use super::{Tree, EndOfFile, Location, Token, Stream};

pub const MISSING_OPEN: &'static str = "Unmatched close bracket";
pub const MISSING_CLOSE: &'static str = "Unmatched open bracket";

// ----------------------------------------------------------------------------

/// A sequence of [`Token`]s enclosed in round brackets.
///
/// The contents should be comma-separated [`Expr`]s, but we allow anything,
/// including errors.
///
/// [`Expr`]: super::welly::Expr
#[derive(Debug)]
pub struct Round(pub Vec<Token>);

impl Round {
    pub fn new(contents: Vec<Token>) -> Box<Self> { Box::new(Self(contents)) }
}

impl Tree for Round {}

/// A sequence of [`Token`]s enclosed in square brackets.
///
/// The contents should be comma-separated [`Expr`]s, but we allow anything,
/// including errors.
///
/// [`Expr`]: super::welly::Expr
#[derive(Debug)]
pub struct Square(pub Vec<Token>);

impl Square {
    pub fn new(contents: Vec<Token>) -> Box<Self> { Box::new(Self(contents)) }
}

impl Tree for Square {}

/// A sequence of [`Token`]s enclosed in curly brackets.
///
/// The contents should be [`Stmt`]s, but we allow anything, including errors.
///
/// [`Stmt`]: super::welly::Stmt
#[derive(Debug)]
pub struct Brace(pub Vec<Token>);

impl Brace {
    pub fn new(contents: Vec<Token>) -> Box<Self> { Box::new(Self(contents)) }
}

impl Tree for Brace {}

// ----------------------------------------------------------------------------

/// A [`Stream`] that matches nested brackets.
///
/// Note that this is not a [`Parse`] implementation, because it is recursive.
///
/// [`Parse`]: super::Parse
pub struct Brackets<F, I> {
    open: char,
    close: char,
    new_bracket: F,
    input: I,
    depth: usize
}

impl<
    F: Fn(Vec<Token>) -> Box<dyn Tree>,
    I: Stream,
> Brackets<F, I> {
    /// Construct a [`Brackets`].
    /// - open - the [`char`] used to open a bracket.
    /// - close - the [`char`] used to close a bracket.
    /// - new_bracket - turns bracket contents into a bracket value.
    ///   The bracket contents are read from `Self`.
    /// - input - a [`Stream`] that contains [`char`]s.
    pub fn new(open: char, close: char, new_bracket: F, input: I) -> Self {
        Self {open, close, new_bracket, input, depth: 0}
    }

    /// Returns the bracket starting at `open`.
    fn parse_bracket(&mut self, open_loc: Location) -> Token {
        let mut contents: Vec<Token> = Vec::new();
        loop {
            let token = self.read();
            if token.is_incomplete() { return token; }
            if token == EndOfFile { return Token::new_err(MISSING_CLOSE, open_loc); }
            if token == self.close {
                let close_loc = token.location();
                let bracket = (&self.new_bracket)(contents);
                return Token::new(bracket, Location {start: open_loc.start, end: close_loc.end});
            }
            contents.push(token);
        }
    }
}

impl<
    F: Fn(Vec<Token>) -> Box<dyn Tree>,
    I: Stream,
> Stream for Brackets<F, I> {
    fn read(&mut self) -> Token {
        let token = self.input.read();
        if token == self.open {
            self.depth += 1;
            return self.parse_bracket(token.location());
        }
        if token == self.close {
            if self.depth == 0 {
                return Token::new_err(MISSING_OPEN, token.location());
            }
            self.depth -= 1;
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
        let mut parser = Brackets::new(
            '(',
            ')',
            |contents| Box::new(Round(contents)),
            Brackets::new(
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
            noop(Brackets::new('(', ')', |contents| {
                let contents = noop(contents.into_iter()).read_all();
                Box::new(Round(contents))
            }, parser))
        }

        /// Wrap 'parser' in a [`Square`] parser.
        fn square(parser: impl Stream) -> impl Stream {
            round(Brackets::new('[', ']', |contents| {
                let contents = round(contents.into_iter()).read_all();
                Box::new(Square(contents))
            }, parser))
        }

        /// Wrap 'parser' in a [`Brace`] parser.
        fn brace(parser: impl Stream) -> impl Stream {
            square(Brackets::new('{', '}', |contents| {
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
