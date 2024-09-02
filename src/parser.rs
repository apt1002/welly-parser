use std::any::{Any};
use std::{fmt};
use std::ops::{Range};

/// A position in source code in a form that can be reported to the user.
/// More precisely, a `Location` represents a contiguous range of bytes of
/// source code.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The byte index where this `Location` begins.
    pub start: usize,
    /// The byte index following this `Location`.
    pub end: usize,
}

impl Location {
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
pub struct Token(pub Location, pub Result<Box<dyn Any>, String>);

impl Token {
    /// Discard the [`Location`], panic on `Err`, and panic if the payload is
    /// not of type `T`.
    ///
    /// This is useful in test code.
    pub fn downcast<T: 'static>(self) -> T {
        *self.1.unwrap().downcast::<T>().unwrap()
    }

    /// Discard the [`Location`], panic on `Ok`, return the error message.
    pub fn unwrap_err(self) -> String {
        self.1.unwrap_err()
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Token")
            .field(&(self.0.start .. self.0.end))
            .finish()
    }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that yields [`Token`].
pub trait TokenIterator: Iterator<Item=Token> {}

impl<I: Iterator<Item=Token>> TokenIterator for I {}

// ----------------------------------------------------------------------------

/// The [`Err`] type of [`Parse::parse()`] and [`Context::read()`].
pub enum Failure {
    /// More input is needed to determine the parse result.
    Incomplete,

    /// The input could not be parsed.
    Error(String),
}

/// Returns `Err(Failure::Error(msg.into()))`.
pub fn fail(msg: &'static str) -> Result<Box<dyn Any>, Failure> {
    Err(Failure::Error(msg.into()))
}

// ----------------------------------------------------------------------------

/// A wrapper around an [`Iterator`] of input [`Token`]s.
///
/// It handles errors, and tracks the [`Location`]s of the input `Token`s
/// that could form part of the next output `Token`.
pub struct Context<I: TokenIterator> {
    /// The stream of input [`Token`]s that have not yet been read.
    input: I,

    /// Non-error [`Token`]s to be returned before reading from [`input`],
    /// in reverse order.
    ///
    /// [`input`]: Self::input
    stack: Vec<(Location, Box<dyn Any>)>,

    /// The [`Location`]s of [`Token`]s that have been read but not yet used to
    /// form an output.
    locs: Vec<Location>,
}

impl<I: TokenIterator> Context<I> {
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

    /// Returns `self.stack.pop()` if possible, otherwise `self.input.next()`.
    fn read_inner(&mut self) -> Option<Token> {
        if let Some((loc, t)) = self.stack.pop() {
            Some(Token(loc, Ok(t)))
        } else {
            self.input.next()
        }
    }

    /// Read the next [`Token`] and internally record its [`Location`].
    /// - Ok(token) - The mext `Token`, unwrapped.
    /// - Err(failure) - A [`Failure`] prevented parsing of the next `Token`.
    pub fn read_any(&mut self) -> Result<Box<dyn Any>, Failure> {
        if let Some(Token(loc, t)) = self.read_inner() {
            self.locs.push(loc);
            t.map_err(Failure::Error)
        } else {
            Err(Failure::Incomplete)
        }
    }

    /// Read the next [`Token`] and internally record its [`Location`], but
    /// only if its payload is of type `T`.
    /// - Ok(Some(token)) - The next `Token` is of type `T`.
    /// - Ok(None) - The next `Token` is not a `T`, and has not been read.
    /// - Err(failure) - A [`Failure`] prevented parsing of the next `Token`.
    pub fn read<T: 'static + Any>(&mut self) -> Result<Option<Box<T>>, Failure> {
        let t = self.read_any()?;
        Ok(match t.downcast::<T>() {
            Ok(t) => Some(t),
            Err(t) => { self.unread_any(t); None },
        })
    }

    /// Pretend we haven't read the most recent [`Token`].
    ///
    /// `token` must be the most recent `Token`. It will be returned by the
    /// next call to `read()`.
    pub fn unread_any(&mut self, token: Box<dyn Any>) {
        let loc = self.pop();
        self.stack.push((loc, token));
    }

    /// Pretend we haven't read the most recent [`Token`].
    pub fn unread<T: 'static + Any>(&mut self, token: Box<T>) {
        self.unread_any(token);
    }
}

// ----------------------------------------------------------------------------

/// Parse a `Self` from a stream of [`Self::Input`]s.
pub trait Parse: Sized {
    /// Read input tokens from `input` and try to make a [`Self::Output`].
    fn parse(
        &self,
        input: &mut Context<impl TokenIterator>,
    ) -> Result<Box<dyn Any>, Failure>;
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that generates items by calling [`Parse::parse()`].
pub struct Parser<P: Parse, I: TokenIterator> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: Context<I>,
}

impl<P: Parse, I: TokenIterator> Parser<P, I> {
    pub fn new(parse: P, input: I) -> Self {
        Self {parse, input: Context::new(input)}
    }
}

impl<P: Parse, I: TokenIterator> Iterator for Parser<P, I> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match self.parse.parse(&mut self.input) {
            Ok(token) => {
                let loc = Location::union(self.input.drain());
                Some(Token(loc, Ok(token)))
            },
            Err(Failure::Incomplete) => {
                let _ = self.input.drain();
                None
            },
            Err(Failure::Error(e)) => {
                let loc = self.input.pop();
                let _ = self.input.drain();
                Some(Token(loc, Err(e.into())))
            },
        }
    }
}
