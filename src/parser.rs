use super::{Tree, Location, Loc, Token, Stream};

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
    stack: Vec<Loc<Box<dyn Tree>>>,

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

    /// Returns the [`Location`] of the first [`Token`] returned by `read()`.
    pub fn first(&self) -> Location {
        *self.locs.first().expect("No tokens have been read")
    }

    /// Returns the [`Location`] of the last [`Token`] returned by `read()`.
    pub fn last(&self) -> Location {
        *self.locs.last().expect("No tokens have been read")
    }

    /// Annotate `t` with `last()`.
    pub fn locate<T>(&self, value: T) -> Loc<T> { Loc(value, self.last()) }

    /// Returns a [`Location`] containing all [`Token`]s `read()` so far, and
    /// forgets them.
    pub fn drain(&mut self) -> Location {
        let ret = Location {start: self.first().start, end: self.last().end};
        self.locs.clear();
        ret
    }

    /// Returns `self.stack.pop()` if possible, otherwise `self.input.read()`.
    fn read_inner(&mut self) -> Token {
        if let Some(Loc(t, loc)) = self.stack.pop() {
            Token::new(t, loc)
        } else {
            self.input.read()
        }
    }

    /// Read the next [`Token`] and internally record its [`Location`].
    ///
    /// - Ok(tree) - The parse [`Tree`] of the next `Token`.
    /// - Err(msg) - An error prevented parsing of the next `Token`.
    pub fn read_any(&mut self) -> Result<Box<dyn Tree>, String> {
        let token = self.read_inner();
        self.locs.push(token.location());
        token.result()
    }

    /// Read the next [`Token`] and internally record its [`Location`], but
    /// only if its parse [`Tree`] is of type `T`.
    ///
    /// - Ok(Some(tree)) - The next `Token`'s parse tree is of type `T`.
    /// - Ok(None) - The next `Token` is not a `T`. It has been `unread()`.
    /// - Err(message) - An error prevented parsing of the next `Token`.
    pub fn read<T: Tree>(&mut self) -> Result<Option<Box<T>>, String> {
        Ok(match self.read_any()?.downcast::<T>() {
            Ok(t) => Some(t),
            Err(t) => { self.unread(t); None },
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
    pub fn unread(&mut self, tree: Box<dyn Tree>) {
        let loc = self.pop();
        self.stack.push(Loc(tree, loc));
    }
}

// ----------------------------------------------------------------------------

/// Parse a [`Stream`].
pub trait Parse: Sized {
    /// Read input [`Tree`]s from `input` and try to make a single output tree.
    ///
    /// Special cases:
    /// - An unrecognised input tree should be passed on unchanged.
    ///   - In particular, [`EndOfFile`] should be passed on unchanged. It must
    ///     never be incorporated into a larger parse tree.
    /// - If this parser finds a parse error, abandon the current parse tree
    ///   and return `Err(message)`.
    /// - If `input` reports a parse error, abandon the current parse tree and
    ///   pass on the error unchanged.
    ///   - In particular, if `input` reports an incomplete file, pass it on.
    ///
    /// [`EndOfFile`]: super::EndOfFile
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String>;

    /// Read [`Token`]s from `input` to make a [`Stream`] of output `Token`s.
    ///
    /// To make each output `Token`, the returned `Stream` calls
    /// [`parse()`] to make a [`Tree`], and annotates it with a [`Location`].
    ///
    /// [`parse()`]: Self::parse()
    fn parse_stream<I: Stream>(self, input: I) -> ParseStream<Self, I> {
        ParseStream {parse: self, input: Context::new(input)}
    }
}

// ----------------------------------------------------------------------------

/// The [`Stream`] returned by `Parse::parse_stream()`.
// TODO: Make private, using a newer version of Rust that supports RPIT.
pub struct ParseStream<P: Parse, I: Stream> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: Context<I>,
}

impl<P: Parse, I: Stream> Stream for ParseStream<P, I> {
    fn read(&mut self) -> Token {
        let ret = self.parse.parse(&mut self.input);
        let last = self.input.last();
        let all = self.input.drain();
        let loc = if ret.is_ok() { all } else { last };
        Token(Loc(ret, loc))
    }
}
