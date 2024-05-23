use std::ops::{Range};
use super::{UndoIterator};

/// A position in source code in a form that can be reported to the user.
/// More precisely, a `Location` represents a contiguous range of bytes of
/// source code.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The byte index where this `Location` begins.
    start: usize,
    /// The byte index following this `Location`.
    end: usize,
}

impl Location {
    /// Returns the smallest `Location` containing all
    pub fn union(pieces: impl IntoIterator<Item=Self>) -> Self {
        let mut pieces = pieces.into_iter();
        let mut ret = pieces.next().expect("Cannot form the union of no pieces");
        while let Some(piece) = pieces.next() {
            ret.start = std::cmp::min(ret.start, piece.start);
            ret.end = std::cmp::min(ret.end, piece.end);
        }
        ret
    }
}

impl From<usize> for Location {
    fn from(value: usize) -> Self { Self {start: value, end: value + 1} }
}

impl From<(usize, usize)> for Location {
    fn from(value: (usize, usize)) -> Self { Self {start: value.0, end: value.1} }
}

impl From<Range<usize>> for Location {
    fn from(value: Range<usize>) -> Self { Self {start: value.start, end: value.end} }
}

// ----------------------------------------------------------------------------

/// Represents a parse tree of type `T` or a parse error, with a [`Location`].
pub struct Token<T>(pub Location, pub Result<T, String>);

impl<T> Token<T> {
    /// Constructs `Self` typically out of smaller `Token`s.
    pub fn compound(locs: impl IntoIterator<Item=Location>, t: impl Into<T>) -> Self {
        Token(Location::union(locs), Ok(t.into()))
    }

    /// Constructs `Self` from a [`Location`] and an error message.
    pub fn error(locs: impl IntoIterator<Item=Location>, e: &str) -> Self {
        Token(Location::union(locs), Err(e.into()))
    }

    /// Preserves the [`Location`] and any error, but applies `f` to a token.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Token<U> {
        Token(self.0, self.1.map(f))
    }

    pub fn into<U>(self) -> Token<U> where T: Into<U> { self.map(T::into) }
}

// ----------------------------------------------------------------------------

/// Parse a `Self` from a stream of [`Self::Input`]s.
pub trait Parse: Sized {
    /// The type of the input tokens.
    type Input;

    /// The type of the output tokens.
    type Output;

    /// Read input tokens from `input` and try to make a `Self::Output`.
    ///
    /// There are three possible return values:
    /// - `None` indicates that not enough input is available.
    /// - `Some(_, Ok(t))` indicates a successful parse with result `t`.
    /// - `Some(_, Err(e))` indicates an unsuccessful parse with error `e`.
    ///   This is also used at the end of the input, if there is no possibility
    ///   of more input becoming available.
    ///
    /// In all cases, items will be irreversibly read from `input`. You may
    /// therefore wish to clone `input` before calling this method.
    fn parse<
        I: Iterator<Item=Token<Self::Input>>,
    >(&self, input: &mut UndoIterator<I>) -> Option<Token<Self::Output>>;

    /// Parse a stream of [`Self::Input`] into a stream of [`Self::Output`].
    fn iter<
        I: Iterator<Item=Token<Self::Input>>,
    >(self, input: I) -> Parser<Self, I> {
        Parser {parse: self, input: UndoIterator::new(input)}
    }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that generates items by calling [`Parse::parse()`].
pub struct Parser<P: Parse, I: Iterator<Item=Token<P::Input>>> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: UndoIterator<I>,
}

impl<P: Parse, I: Iterator<Item=Token<P::Input>>> Iterator for Parser<P, I> {
    type Item = Token<P::Output>;
    fn next(&mut self) -> Option<Self::Item> { self.parse.parse(&mut self.input) }
}
