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
pub struct Token<T>(pub Location, pub Result<T, String>);

impl<T> Token<T> {
    pub fn into<U>(self) -> Token<U> where T: Into<U> { Token(self.0, self.1.map(T::into)) }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that yields [`Token<Self::T>`].
pub trait TokenIterator: Iterator<Item=Token<Self::T>> {
    /// The type of [`Token`] returned by this [`TokenIterator`].
    type T;
}

// ----------------------------------------------------------------------------

/// The [`Err`] type of [`Parse::parse()`] and [`Context::read()`].
pub enum Failure {
    /// More input is needed to determine the parse result.
    Incomplete,

    /// The input could not be parsed.
    Error(String),
}

/// Returns `Err(Failure::Error(msg.into()))`.
pub fn fail<T>(msg: &'static str) -> Result<T, Failure> {
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
    stack: Vec<(Location, I::T)>,

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

    /// Returns the union of the [`Location`]s of all recent [`Token`]s and
    /// forgets them.
    pub fn drain(&mut self) -> Location { Location::union(self.locs.drain(..)) }

    /// Returns `self.stack.pop()` if possible, otherwise `self.input.next()`.
    fn read_inner(&mut self) -> Option<I::Item> {
        if let Some((loc, t)) = self.stack.pop() {
            Some(Token(loc, Ok(t)))
        } else {
            self.input.next()
        }
    }

    /// Read the next [`Token`] and internally record its [`Location`].
    pub fn read(&mut self) -> Result<I::T, Failure> {
        if let Some(Token(loc, t)) = self.read_inner() {
            self.locs.push(loc);
            t.map_err(Failure::Error)
        } else {
            Err(Failure::Incomplete)
        }
    }

    /// Read [`Token`]s until one matches `is_wanted`. Internally record its
    /// [`Location`].
    pub fn read_until(&mut self, mut is_wanted: impl FnMut(&I::T) -> bool) -> Result<I::T, Failure> {
        let mut t = self.read()?;
        while !is_wanted(&t) {
            let _ = self.pop();
            t = self.read()?;
        }
        Ok(t)
    }

    /// Pretend we haven't read the most recent [`Token`].
    ///
    /// `token` must be the most recent `Token`. It will be returned by the
    /// next call to `read()`.
    pub fn unread(&mut self, token: I::T) {
        let loc = self.pop();
        self.stack.push((loc, token));
    }
}

// ----------------------------------------------------------------------------

/// Parse a `Self` from a stream of [`Self::Input`]s.
pub trait Parse: Sized {
    /// The type of the input tokens.
    type Input;

    /// The type of the output tokens.
    type Output;

    /// Read input tokens from `input` and try to make a [`Self::Output`].
    fn parse(
        &self,
        input: &mut Context<impl TokenIterator<T=Self::Input>>,
    ) -> Result<Self::Output, Failure>;
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that generates items by calling [`Parse::parse()`].
pub struct Parser<P: Parse, I: TokenIterator<T=P::Input>> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: Context<I>,
}

impl<P: Parse, I: TokenIterator<T=P::Input>> Parser<P, I> {
    pub fn new(parse: P, input: I) -> Self {
        Self {parse, input: Context::new(input)}
    }
}

impl<P: Parse, I: TokenIterator<T=P::Input>> Iterator for Parser<P, I> {
    type Item = Token<P::Output>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.parse.parse(&mut self.input) {
            Ok(token) => {
                Some(Token(self.input.drain(), Ok(token)))
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

impl<P: Parse, I: TokenIterator<T=P::Input>> TokenIterator for Parser<P, I> {
    type T = P::Output;
}
