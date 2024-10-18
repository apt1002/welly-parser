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
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{}..{}", self.start, self.end))
    }
}

impl From<Range<usize>> for Location {
    fn from(value: Range<usize>) -> Self { Self {start: value.start, end: value.end} }
}

// ----------------------------------------------------------------------------

/// Represents a `T` with a [`Location`].
///
/// This is commonly used to represent bits of a parse tree, remembering where
/// they came from in the source code.
#[derive(Debug, Copy, Clone)]
pub struct Loc<T>(pub T, pub Location);

impl<T> Loc<T> {
    /// Convert an `&Loc<T>` to a `Loc<&T>`.
    pub fn as_ref(&self) -> Loc<&T> { Loc(&self.0, self.1) }
}

impl<U, T: PartialEq<U>> PartialEq<U> for Loc<T> {
    fn eq(&self, other: &U) -> bool { self.0 == *other }
}

// ----------------------------------------------------------------------------

/// Represents a parse [`Tree`] or a parse error, with a [`Location`].
///
/// - Token(Loc(Ok(t), location)) represents a parse-tree `t`.
///   `t` can be [`EndOfFile`] to represent the end of the source code.
///   In this case, the `Location` is spurious.
/// - Token(Loc(Err(e), location)) represents an error message `e`.
///   `e` can be the empty string to mark the end of incomplete source code.
///   In this case, the `Location` is spurious.
#[derive(Debug)]
pub struct Token(pub Loc<Result<Box<dyn Tree>, String>>);

impl Token {
    /// Constructs a `Self` from a `Tree` and its `Location`.
    pub fn new(tree: Box<dyn Tree>, location: impl Into<Location>) -> Self {
        Token(Loc(Ok(tree), location.into()))
    }

    /// Constructs a `Self` from an error message and its `Location`.
    pub fn new_err(message: impl Into<String>, location: impl Into<Location>) -> Self {
        Token(Loc(Err(message.into()), location.into()))
    }

    /// Returns an `EndOfFile`, to indicate the end of the source code.
    pub fn end_of_file() -> Self { Self::new(Box::new(EndOfFile), Location::EVERYWHERE) }

    /// Returns an empty error message, to indicate incomplete source code.
    pub fn incomplete() -> Self { Self::new_err("", Location::EVERYWHERE) }

    /// Returns the [`Location`] of `self`.
    pub fn location(&self) -> Location { self.0.1 }

    /// Throws away the `location`.
    pub fn result(self) -> Result<Box<dyn Tree>, String> { self.0.0 }

    /// Throws away the `location`.
    pub fn result_ref(&self) -> &Result<Box<dyn Tree>, String> { &self.0.0 }

    /// Tests whether `self` is a `T`.
    pub fn is<T: Tree>(&self) -> bool {
        if let Ok(t) = self.result_ref() { t.is::<T>() } else { false }
    }

    /// Tests whether `self` marks the end of incomplete source code.
    pub fn is_incomplete(&self) -> bool {
        if let Err(e) = self.result_ref() { e.len() == 0 } else { false }
    }

    /// Discard the [`Location`], panic on `Err`, and panic if the payload is
    /// not of type `T`.
    ///
    /// This is useful in test code.
    pub fn unwrap<T: Tree>(self) -> T {
        *self.result().unwrap().downcast::<T>().unwrap()
    }

    /// Discard the [`Location`], panic on `Ok`, return the error message.
    ///
    /// This is useful in test code.
    pub fn unwrap_err(self) -> String {
        self.result().unwrap_err()
    }
}

impl<T: Tree + PartialEq> std::cmp::PartialEq<T> for Token {
    fn eq(&self, other: &T) -> bool {
        if let Ok(t) = self.result_ref() { **t == *other } else { false }
    }
}

// ----------------------------------------------------------------------------

/// Yields [`Token`]s.
///
/// Differences from an [`Iterator`]:
/// - The item type is always [`Token`].
/// - `read()` always returns an item.
pub trait Stream {
    /// Read a single `Token`.
    fn read(&mut self) -> Token;

    /// Read and return all `Token`s upto [`EndOfFile`], which is discarded.
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
        self.next().unwrap_or_else(|| Token::end_of_file())
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
    ///   `true` gives `Token::end_of_file()`, otherwise `Token::incomplete()`.
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
            Token::new(Box::new(c), start..end)
        } else if self.is_complete { Token::end_of_file() } else { Token::incomplete() }
    }
}
