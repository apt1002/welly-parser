use std::{fmt};
use std::ops::{Range};
use std::str::{Chars};

use super::{Tree, EndOfFile};

/// A position in source code in a form that can be reported to the user.
/// More precisely, a `Location` represents a contiguous range of bytes of
/// source code.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The byte index where this `Location` begins.
    pub start: usize,
    /// The byte index following this `Location`.
    pub end: usize,
}

impl Location {
    /// A dummy value that can be used for things like [`EndOfFile`].
    pub const EVERYWHERE: Location = Location {start: usize::MIN, end: usize::MAX};

    /// Returns the smallest `Location` containing all `pieces`.
    pub fn union(pieces: impl IntoIterator<Item=Self>) -> Self {
        let mut pieces = pieces.into_iter();
        let mut ret = pieces.next().expect("Cannot form the union of no pieces");
        while let Some(piece) = pieces.next() {
            ret.start = std::cmp::min(ret.start, piece.start);
            ret.end = std::cmp::max(ret.end, piece.end);
        }
        ret
    }
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{}..{}", self.start, self.end))
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

/// Represents a parse [`Tree`] or a parse error, with a [`Location`].
///
/// - Token(loc, Ok(t)) represents a parse-tree `t`.
///   `t` can be [`EndOfFile`] to represent the end of the source code.
///   In this case, the `Location` is spurious.
/// - Token(loc, Err(e)) represents an error message `e`.
///   `e` can be the empty string to mark the end of incomplete source code.
///   In this case, the `Location` is spurious.
#[derive(Debug)]
pub struct Token(pub Location, pub Result<Box<dyn Tree>, String>);

impl Token {
    /// Returns an `EndOfFile`, to indicate the end of the source code.
    fn end_of_file() -> Self { Self(Location::EVERYWHERE, Ok(Box::new(EndOfFile))) }

    /// Returns an empty error message, to indicate incomplete source code.
    fn incomplete() -> Self { Self(Location::EVERYWHERE, Err("".into())) }

    /// If `self` is `Token(_, Ok(t))` and `t` is of type `T`, return it.
    pub fn downcast_copy<T: Tree + Copy>(&self) -> Option<T> {
        if let Token(_, Ok(t)) = self { t.downcast_ref().copied() } else { None }
    }

    /// Tests whether `self` is a `T`.
    pub fn is<T: Tree>(&self) -> bool {
        if let Token(_, Ok(t)) = self { t.downcast_ref::<T>().is_some() } else { false }
    }

    /// Tests whether `self` marks the end of incomplete source code.
    pub fn is_incomplete(&self) -> bool {
        if let Token(_, Err(e)) = self { e.len() == 0 } else { false }
    }

    /// Discard the [`Location`], panic on `Err`, and panic if the payload is
    /// not of type `T`.
    ///
    /// This is useful in test code.
    pub fn unwrap<T: Tree>(self) -> T {
        *self.1.unwrap().downcast::<T>().unwrap()
    }

    /// Discard the [`Location`], panic on `Ok`, return the error message.
    ///
    /// This is useful in test code.
    pub fn unwrap_err(self) -> String {
        self.1.unwrap_err()
    }
}

impl<T: Tree + PartialEq> std::cmp::PartialEq<T> for Token {
    fn eq(&self, other: &T) -> bool {
        if let Token(_, Ok(t)) = self { t.downcast_ref::<T>() == Some(other) } else { false }
    }
}

// ----------------------------------------------------------------------------

/// Yields [`Token`]s.
pub trait Stream {
    /// Read a single `Token`.
    fn read(&mut self) -> Token;

    /// Read all `Token`s, upto and excluding [`EndOfFile`].
    fn read_all(mut self) -> Vec<Token> where Self: Sized {
        let mut ret = Vec::new();
        let mut token = self.read();
        while token != EndOfFile {
            ret.push(token);
            token = self.read();
        }
        ret
    }
}

impl<I: Iterator<Item=Token>> Stream for I {
    fn read(&mut self) -> Token {
        self.next().unwrap_or_else(
            || Token(Location::EVERYWHERE, Ok(Box::new(EndOfFile)))
        )
    }
}

// ----------------------------------------------------------------------------

/// A [`Stream`] through a [`str`].
///
/// The [`Token`]s are `char`s. Their [`Location`]s are relative to the `str`.
///
/// The `Stream` is terminated with [`Token::end_of_file()`] if `is_complete`,
/// otherwise with [`Token::incomplete()`].
pub struct Characters<'a> {
    /// An Iterator through the source code.
    chars: Chars<'a>,

    /// The byte length of the source code.
    length: usize,

    /// `true` for `Token::end_of_file()`, otherwise `Token::incomplete()`.
    is_complete: bool,
}

impl<'a> Characters<'a> {
    /// Iterate through `source`.
    ///
    /// - is_complete - Determines the `Token` appended to the end of `source`.
    ///   `true` for `Token::end_of_file()`, otherwise `Token::incomplete()`.
    pub fn new(source: &'a str, is_complete: bool) -> Self {
        Self {chars: source.chars(), length: source.len(), is_complete}
    }

    /// Returns the current byte index in the `str`.
    pub fn index(&self) -> usize { self.length - self.chars.as_str().len() }
}

impl<'a> Stream for Characters<'a> {
    fn read(&mut self) -> Token {
        let start = self.index();
        if let Some(c) = self.chars.next() {
            let end = self.index();
            Token(Location {start, end}, Ok(Box::new(c)))
        } else if self.is_complete { Token::end_of_file() } else { Token::incomplete() }
    }
}
