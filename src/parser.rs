use std::{fmt};
use std::ops::{Range};

use super::{Tree};

/// Represents the end of the source code.
///
/// Parsers must return this [`Tree`] unchanged. It must never be incorporated
/// into a larger [`Tree`].
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct EndOfFile;

impl Tree for EndOfFile {}

// ----------------------------------------------------------------------------

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

/// A high-level wrapper around an input [`Stream`].
///
/// It handles errors, and tracks the [`Location`]s of the input `Token`s
/// that could form part of the next output `Token`. It also provides an
/// `unread()` method to pretend that you didn't read a `Token`.
pub struct Context<I: Stream> {
    /// The input [`Stream`].
    input: I,

    /// Non-error [`Token`]s to be returned before reading from [`input`],
    /// in reverse order.
    ///
    /// [`input`]: Self::input
    stack: Vec<(Location, Box<dyn Tree>)>,

    /// The [`Location`]s of [`Token`]s that have been read but not yet used to
    /// form an output.
    locs: Vec<Location>,
}

impl<I: Stream> Context<I> {
    pub fn new(input: I) -> Self {
        Self {input, stack: Vec::new(), locs: Vec::new()}
    }

    /// Returns the [`Location`] of the most recent [`Token`], and forgets it.
    pub fn pop(&mut self) -> Location {
        self.locs.pop().expect("No tokens have been read")
    }

    /// Returns an iterator over the [`Location`]s of all recent [`Token`]s and
    /// forgets them.
    pub fn drain(&mut self) -> impl Iterator<Item=Location> + '_ { self.locs.drain(..) }

    /// Returns `self.stack.pop()` if possible, otherwise `self.input.read()`.
    fn read_inner(&mut self) -> Token {
        if let Some((loc, t)) = self.stack.pop() {
            Token(loc, Ok(t))
        } else {
            self.input.read()
        }
    }

    /// Read the next [`Token`] and internally record its [`Location`].
    ///
    /// - Ok(tree) - The parse [`Tree`] of the next `Token`.
    /// - Err(msg) - An error prevented parsing of the next `Token`.
    pub fn read_any(&mut self) -> Result<Box<dyn Tree>, String> {
        let Token(loc, t) = self.read_inner();
        self.locs.push(loc);
        t
    }

    /// Read the next [`Token`] and internally record its [`Location`], but
    /// only if its parse [`Tree`] is of type `T`.
    ///
    /// - Ok(Some(tree)) - The next `Token`'s parse tree is of type `T`.
    /// - Ok(None) - The next `Token` is not a `T`, and has not been read.
    /// - Err(message) - An error prevented parsing of the next `Token`.
    pub fn read<T: Tree>(&mut self) -> Result<Option<Box<T>>, String> {
        Ok(match self.read_any()?.downcast::<T>() {
            Ok(t) => Some(t),
            Err(t) => { self.unread_any(t); None },
        })
    }

    /// Read the next [`Token`] and internally record its [`Location`], but
    /// only if it `is_wanted`.
    /// - Ok(Some(tree)) - If `is_wanted(tree)`.
    /// - Ok(None) - The next `Token`'s parse tree is not a `T` or is unwanted.
    ///   It has been `unread()`.
    /// - Err(message) - An error prevented parsing of the next `Token`.
    pub fn read_if<T: Tree>(
        &mut self,
        is_wanted: impl FnOnce(&T) -> bool,
    ) -> Result<Option<Box<T>>, String> {
        Ok(self.read::<T>()?.and_then(
            |t| if is_wanted(&*t) { Some(t) } else { self.unread(t); None }
        ))
    }

    /// Pretend we haven't read the most recent [`Token`].
    ///
    /// `tree` must be the parse [`Tree`] of the most recent `Token`. It will
    /// be returned by the next call to `read()`.
    pub fn unread_any(&mut self, tree: Box<dyn Tree>) {
        let loc = self.pop();
        self.stack.push((loc, tree));
    }

    /// Pretend we haven't read the most recent [`Token`].
    pub fn unread<T: Tree>(&mut self, tree: Box<T>) {
        self.unread_any(tree);
    }
}

// ----------------------------------------------------------------------------

/// Parse a [`Stream`].
pub trait Parse: Sized {
    /// Read input [`Tree`]s from `input` and try to make a single output tree.
    ///
    /// Special cases:
    /// - An unrecognised input tree should be passed on unchanged.
    /// - In particular, [`EndOfFile`] should be passed on unchanged. It must
    ///   never be incorporated into a larger parse tree.
    /// - If this parser finds a parse error, abandon the current parse tree
    ///   and return `Err(message)`.
    /// - If `input` reports a parse error, abandon the current parse tree and
    ///   pass on the error unchanged.
    /// - In particular, if `input` reports an incomplete file, pass it on.
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String>;

    /// Read [`Token`]s from `input` to make a [`Stream`] of output `Token`s.
    ///
    /// To make each output `Token`, the returned `Stream` calls [`parse()`] to
    /// make a [`Tree`], and annotates it with a [`Location`].
    fn parse_stream<I: Stream>(self, input: I) -> Parser<Self, I> {
        Parser {parse: self, input: Context::new(input)}
    }
}

// ----------------------------------------------------------------------------

/// The [`Stream`] returned by `Parse::parse_stream()`.
pub struct Parser<P: Parse, I: Stream> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: Context<I>,
}

impl<P: Parse, I: Stream> Stream for Parser<P, I> {
    fn read(&mut self) -> Token {
        match self.parse.parse(&mut self.input) {
            Ok(token) => {
                let loc = Location::union(self.input.drain());
                Token(loc, Ok(token))
            },
            Err(e) => {
                let loc = self.input.pop();
                let _ = self.input.drain();
                Token(loc, Err(e.into()))
            },
        }
    }
}
