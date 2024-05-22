use std::iter::{Peekable};
use super::{Location};

/// Represents a parse tree of type `T` or a parse error, with a [`Location`].
pub type Token<T> = (Location, Result<T, String>);

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
    fn parse<I: Iterator<Item=Self::Input>>(&self, input: &mut Peekable<I>) -> Option<Token<Self::Output>>;

    /// Parse a stream of [`Self::Input`] into a stream of [`Self::Output`].
    fn iter<I: Iterator<Item=Self::Input>>(self, input: I) -> Parser<Self, I> {
        Parser {parse: self, input: input.peekable()}
    }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] that generates items by calling [`Parse::parse()`].
pub struct Parser<P: Parse, I: Iterator<Item=P::Input>> {
    /// The parsing function.
    parse: P,

    /// The input stream.
    input: Peekable<I>,
}

impl<P: Parse, I: Iterator<Item=P::Input>> Iterator for Parser<P, I> {
    type Item = Token<P::Output>;
    fn next(&mut self) -> Option<Self::Item> { self.parse.parse(&mut self.input) }
}
