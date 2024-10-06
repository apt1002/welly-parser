use std::rc::{Rc};

use super::{bracket, stmt, EndOfFile, Location, Token, Stream, Parser};

/// Read [`Token`]s from `stream` until finding one that heuristically might be
/// the end of a `Stmt`, and return its [`Location`] if successful.
///
/// Use this only to recover after an error, because it discards source code.
fn skip(stream: &mut impl Stream) -> Option<Location> {
    loop {
        let token = stream.read();
        if token.is_incomplete() || token.is::<EndOfFile>() { return None; }
        if let Some(c) = token.downcast_copy::<char>() {
            if c == ';' { return Some(token.0); }
        }
        if token.is::<bracket::Brace>() { return Some(token.0); }
        if token.is::<stmt::Stmt>() {
            // Oops! We read too far. Oh well, discard it.
            return Some(token.0);
        }
    }
}

// ----------------------------------------------------------------------------

/// A growable source file that can be parsed incrementally.
#[derive(Default, Debug)]
pub struct Buffer {
    /// The parser.
    pub parser: Parser,

    /// Source code that has been received but not yet parsed.
    pub source: String,

    /// `true` if all source code has been received.
    pub is_complete: bool,
}

impl Buffer {
    /// Returns the suffix of the source code that has not yet been parsed.
    pub fn remainder(&self) -> &str { &self.source }

    /// Append `source` to the source code.
    pub fn push_str(&mut self, source: &str) {
        assert!(!self.is_complete);
        self.source.push_str(source);
    }

    /// Inform `self` that it has all the source code.
    pub fn complete(&mut self) { self.is_complete = true; }

    /// Attempt to parse [`self.remainder()`]. Hopefully the returned [`Token`]
    /// is a [`Stmt`].
    ///
    /// `Some((source, token))` indicates that there was enough source code to
    /// parse a `Token` (which might be an error message). [`Location`]s are
    /// relative to the returned `source`, which is removed from `self`.
    ///
    /// `None` indicates that there was not enough source code, either because
    /// we need to wait for more, or because there is no more. In this case
    /// `self` is not modified.
    pub fn try_parse(&mut self) -> Option<(Rc<str>, Token)> {
        let (token, end) = {
            let mut stream = self.parser.parse(self.remainder(), self.is_complete);
            let token = stream.read();
            if token.is_incomplete() || token.is::<EndOfFile>() { return None; }
            // Split off some source code including at least `token.0`.
            let end = match &token.1 {
                Ok(_) => token.0.end,
                Err(_) => if let Some(loc) = skip(&mut stream) { loc.end } else { token.0.end },
            };
            (token, end)
        };
        let s: String = self.source.drain(..end).collect();
        Some((s.into(), token))
    }
}
