use super::{Tree, Location, Token, Stream};

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
    ///
    /// [`EndOfFile`]: super::EndOfFile
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String>;

    /// Read [`Token`]s from `input` to make a [`Stream`] of output `Token`s.
    ///
    /// To make each output `Token`, the returned `Stream` calls
    /// [`self.parse()`] to make a [`Tree`], and annotates it with a
    /// [`Location`].
    fn parse_stream<I: Stream>(self, input: I) -> Parser<Self, I> {
        Parser {parse: self, input: Context::new(input)}
    }
}

// ----------------------------------------------------------------------------

/// The [`Stream`] returned by `Parse::parse_stream()`.
// TODO: Make private, using a newer version of Rust that supports RPIT.
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
