use super::{Location, Result};

// ----------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Token<T> {
    /// A successfully parsed token.
    Token(Location, T),

    /// A syntax error.
    Syntax(Location, String),
}

// ----------------------------------------------------------------------------

/// A peekable stream of [`Self::Item`]s.
///
/// This is similar to an [`Iterator`], except:
/// - It has a `peek()` method.
/// - Its [`Self::Item`]s have [`Location`]s.
/// - It represents the end of the stream using [`Error::End`].
/// - It can return other errors.
///
/// [`Error::End`]: super::Error::End
pub trait Stream {
    /// The type of items produced by this `Stream`.
    type Item;

    /// Returns the next `T`, if any, without consuming it.
    /// The next call to `take` will return the same value.
    fn peek(&mut self) -> Result<&Token<Self::Item>>;

    /// Consumes and returns the next `T`, if any.
    fn take(&mut self) -> Result<Token<Self::Item>>;
}

impl<'a, S> Stream for &'a mut S where S: Stream {
    type Item = S::Item;
    fn peek(&mut self) -> Result<&Token<Self::Item>> { (*self).peek() }
    fn take(&mut self) -> Result<Token<Self::Item>> { (*self).take() }
}

// ----------------------------------------------------------------------------

/// Parse [`Self`] into [`Self::Output`]s.
pub trait Parse: Stream {
    /// The type of token produced by [`parse()`].
    type Output;

    /// Read input tokens from `Self` and try to make a `Self::Output`.
    ///
    /// There are three possible return values:
    /// - `Err(Incomplete)` indicates that not enough input is available.
    /// - `Ok(Token::Token(_, t))` indicates a successful parse with result `t`.
    /// - `Ok(Token::Syntax(_, e))` indicates an unsuccessful parse with error `e`.
    ///   This is also used at the end of the input, if there is no possibility
    ///   of more input becoming available.
    fn parse(&mut self) -> Result<Token<Self::Output>>;
}

// ----------------------------------------------------------------------------

/// A [`Stream`] that generates items by calling [`Parse::parse()`] on an input
/// `Stream`.
pub struct ParseStream<P: Parse> {
    /// The input stream.
    input: P,

    /// The next output token, if it has been parsed.
    next: Option<Token<P::Output>>,
}

impl<P: Parse> ParseStream<P> {
    fn new(input: P) -> Self { Self {input, next: None} }

    /// Generate the next output token, if necessary and possible, and return
    /// `&mut self.next`.
    ///
    /// If this method returns [`Ok`], [`self.next`] is guaranteed to be
    /// an [`Option::Some`].
    fn next(&mut self) -> Result<&mut Option<Token<P::Output>>> {
        if self.next.is_none() { self.next = Some(self.input.parse()?); }
        Ok(&mut self.next)
    }
}

impl<P: Parse> Stream for ParseStream<P> {
    type Item = P::Output;
    fn peek(&mut self) -> Result<&Token<Self::Item>> { Ok(self.next()?.as_ref().unwrap()) }
    fn take(&mut self) -> Result<Token<Self::Item>> { Ok(self.next()?.take().unwrap()) }
}
