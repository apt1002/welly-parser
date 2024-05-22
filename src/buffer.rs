use super::{Token, Result};

/// A growable source file.
pub struct Buffer {
    /// All source code received so far.
    pub source: String,

    /// The byte index up to which we've successfully parsed.
    pos: usize,
}

impl Buffer {
    /// Attempt to parse the remainder of `self` using `parse`, leaving the
    /// cursor in its original position if `parse` returns [`Incomplete`]
    fn try_parse<T>(
        &mut self,
        parse: impl FnOnce(&mut CharacterStream) -> Result<T>,
    ) -> Result<T> {
        let mut stream = CharacterStream::new(&mut self.source, self.pos);
        let ret = parse(&mut stream)?;
        self.pos = stream.pos;
        Ok(ret)
    }

    /// Parse and throw away a whitespace string.
    fn skip_whitespace(&mut self) {
        self.try_parse(|_cs: &mut CharacterStream| Ok(()));
    }

    /// Parse and return a [`Token<Statement>`].
    fn parse(&mut self) -> Result<Token<Statement>> {
        self.try_parse(|_cs: &mut CharacterStream| todo!())
    }
}

// ----------------------------------------------------------------------------

/// Stub.
pub struct Statement;

/// Stub.
pub struct CharacterStream<'a> {
    source: &'a mut str,
    pos: usize,
}

impl<'a> CharacterStream<'a> {
    pub fn new(source: &'a mut str, pos: usize) -> Self { Self {source, pos} }
}
