use std::str::{Chars};

use super::{Location, Token};

/// A growable source file.
pub struct Buffer {
    /// All source code received so far.
    pub source: String,

    /// The byte index up to which we've successfully parsed.
    pub index: usize,
}

impl Buffer {
    /// Attempt to parse [`self.remainder()`] using `parse`, leaving `index`
    /// unchanged if `parse` returns [`None`]
    fn try_parse<T>(
        &mut self,
        parse: impl FnOnce(&mut Characters) -> Option<T>,
    ) -> Option<T> {
        let mut stream = Characters::new(self.remainder());
        let ret = parse(&mut stream);
        if ret.is_some() { self.index += stream.index(); }
        ret
    }

    /// Returns the suffix of [`self.source`] that has not yet been parsed.
    fn remainder(&self) -> &str { &self.source[self.index..] }

    /// Parse and throw away a whitespace string.
    fn skip_whitespace(&mut self) {
        self.try_parse(|_cs: &mut Characters| Some(()));
    }

    /// Parse and return a [`Token<Statement>`].
    ///
    /// [`Location`]s in the `Token` are relative to [`self.index`] on entry.
    fn parse(&mut self) -> Option<Token<Statement>> {
        self.try_parse(|cs: &mut Characters| cs.next())
    }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] through a [`str`] that returns [`Token<char>`]s.
///
/// The [`Location`]s in the returned `Token`s are relative to the `str`.
pub struct Characters<'a> {
    /// An Iterator through the source code.
    chars: Chars<'a>,

    /// The byte length of the source code.
    length: usize,
}

impl<'a> Characters<'a> {
    /// Iterate through `source`.
    pub fn new(source: &'a str) -> Self {
        Self {chars: source.chars(), length: source.len()}
    }

    /// Returns the current byte index in the `str`.
    pub fn index(&self) -> usize { self.length - self.chars.as_str().len() }
}

impl<'a> Iterator for Characters<'a> {
    type Item = Token<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.index();
        let c = self.chars.next();
        let end = self.index();
        c.map(|c| (Location::from(start..end), Ok(c)))
    }
}

// ----------------------------------------------------------------------------

/// Stub.
pub type Statement = char;
