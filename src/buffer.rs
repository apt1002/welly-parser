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
    /// Returns the suffix of [`self.source`] that has not yet been parsed.
    pub fn remainder(&self) -> &str { &self.source[self.index..] }

    /// Attempt to parse [`self.remainder()`] using `parse`, leaving `index`
    /// unchanged if `parse` returns [`None`]
    fn try_parse(
        &mut self,
        parse: impl FnOnce(&mut Characters) -> Option<Token>,
    ) -> Option<Token> {
        let mut stream = Characters::new(self.remainder());
        let ret = parse(&mut stream);
        if let Some(Token(location, _)) = ret { self.index += location.end; }
        ret
    }

    /// Parse and throw away a whitespace string.
    pub fn skip_whitespace(&mut self) {
        // TODO.
        self.try_parse(|_cs: &mut Characters| Some(Token(Location::from(0), Ok(Box::new(())))));
    }

    /// Parse and return a [`Statement`].
    ///
    /// [`Location`]s in the `Token` are relative to [`self.index`] on entry.
    pub fn parse(&mut self) -> Option<Token> {
        // TODO.
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
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.index();
        let c = self.chars.next();
        let end = self.index();
        c.map(|c| Token(Location::from(start..end), Ok(Box::new(c))))
    }
}
