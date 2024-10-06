use super::{Location, Token, Characters};

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
