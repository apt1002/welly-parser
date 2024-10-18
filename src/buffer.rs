use std::rc::{Rc};

use super::{welly, parsers, EndOfFile, Location, Token, Stream, Characters, Parse};

/// Pipes `source` (which should produce [`char`]s) through:
/// - a lexer,
/// - `word_parser`,
/// - two bracket matchers,
/// - an [`Expr`] parser, and
/// - (if the tightest brackets are not round) a [`Stmt`] parser.
fn make_parser<'a>(source: impl 'a + Stream, word_parser: &'a parsers::Word) -> impl 'a + Stream {
    let stream = parsers::LEXER.parse_stream(source);
    let stream = word_parser.parse_stream(stream);
    parsers::brace(stream)
}

/// Read [`Token`]s from `stream` until finding one that heuristically might be
/// the end of a `Stmt`, and return its [`Location`] if successful.
///
/// Use this only to recover after an error, because it discards source code.
fn skip(stream: &mut impl Stream) -> Option<Location> {
    loop {
        let token = stream.read();
        if token.is_incomplete() || token.is::<EndOfFile>() { return None; }
        if token == ';' { return Some(token.location()); }
        if token.is::<welly::Brace>() { return Some(token.location()); }
        if token.is::<welly::Stmt>() {
            // Oops! We read too far. Oh well, discard it.
            return Some(token.location());
        }
    }
}

// ----------------------------------------------------------------------------

/// A growable source file that can be parsed incrementally.
///
/// ```
/// let mut buffer = welly_parser::Buffer::default();
/// buffer.push_str("hw = \"Hello, world!\\n\";\n");
/// buffer.push_str("for _ in 10 { print(hw); }");
/// while let Some(token) = buffer.try_parse() {
///     println!("{:#?}", token);
/// }
/// ```
#[derive(Debug)]
pub struct Buffer {
    /// A cache of [`parsers::word()`].
    word_parser: parsers::Word,

    /// Source code that has been received but not yet parsed.
    source: String,

    /// `true` if all source code has been received.
    is_complete: bool,
}

impl Default for Buffer {
    fn default() -> Self {
        Self {word_parser: parsers::word(), source: String::new(), is_complete: false}
    }
}

impl Buffer {
    /// Returns the suffix of the source code that has not yet been parsed.
    pub fn remainder(&self) -> &str { &self.source }

    /// Append `source` to the source code. Requires `!self.is_complete()`.
    pub fn push_str(&mut self, source: &str) {
        assert!(!self.is_complete());
        self.source.push_str(source);
    }

    /// Inform `self` that it has all the source code.
    ///
    /// This can be important, as in the following example:
    /// ```
    /// let mut buffer = welly_parser::Buffer::default();
    /// buffer.push_str("if c {}"); // Could be followed by `else`.
    /// assert!(buffer.try_parse().is_none());
    /// buffer.complete(); // Exclude `else`.
    /// assert!(buffer.try_parse().is_some());
    /// ```
    pub fn complete(&mut self) { self.is_complete = true; }

    /// Returns `true` if more source code can be added with `self.push_str()`.
    pub fn is_complete(&self) -> bool { self.is_complete }

    /// Attempt to parse [`self.remainder()`]. Hopefully the returned [`Token`]
    /// is a [`Stmt`]. Other possibilities can be found in [`welly`].
    ///
    /// `Some((source, token))` indicates that there was enough source code to
    /// parse a `Token` (which might be an error message). [`Location`]s are
    /// relative to the returned `source`, which is removed from `self`.
    ///
    /// `None` indicates that there was not enough source code, either because
    /// we need to wait for more, or because there is no more. In this case
    /// `self` is not modified.
    ///
    /// [`Stmt`]: welly::Stmt
    pub fn try_parse(&mut self) -> Option<(Rc<str>, Token)> {
        let (token, end) = {
            let source = Characters::new(self.remainder(), self.is_complete);
            let mut stream = make_parser(source, &self.word_parser);
            let token = stream.read();
            if token.is_incomplete() || token.is::<EndOfFile>() { return None; }
            // Split off some source code including at least `token.0`.
            let mut end = token.location().end;
            if token.result_ref().is_err() { if let Some(loc) = skip(&mut stream) { end = loc.end; } }
            (token, end)
        };
        let s: String = self.source.drain(..end).collect();
        Some((s.into(), token))
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn check(
        source: &'static str,
        is_complete: bool,
        expected: impl Into<Vec<&'static str>>,
        expected_remainder: &'static str,
    ) {
        let mut buffer = Buffer::default();
        buffer.push_str(source);
        if is_complete { buffer.complete(); }
        let mut tokens: Vec<String> = Vec::new();
        while let Some((s, token)) = buffer.try_parse() {
            let loc = token.location();
            let span = String::from(&s[loc.start..loc.end]);
            tokens.push(span);
        }
        assert_eq!(tokens, expected.into());
        assert_eq!(buffer.remainder(), expected_remainder);
    }

    #[test]
    fn whitespace() {
        check(" ", true, [], " ");
    }

    #[test]
    fn semicolon() {
        check(" ; ", true, [";"], " ");
    }

    #[test]
    fn five() {
        check(" 5; ", true, ["5;"], " ");
    }

    #[test]
    fn if_() {
        check("if b {}", true, ["if b {}"], "");
        check("if b {}", false, [], "if b {}");
        check("if b {};", false, ["if b {}", ";"], "");
    }

    #[test]
    fn if_else() {
        check("if b {} else {}", true, ["if b {} else {}"], "");
        check("if b {} else {}", false, ["if b {} else {}"], "");
        check("if b {} else {};", false, ["if b {} else {}", ";"], "");
    }

    #[test]
    fn fn_() {
        check("fn f() {}\nx; y", true, ["fn f() {}\nx;", "y"], "");
        check("fn f() {}\nx; y", false, ["fn f() {}\nx;"], " y");
        check("fn f() {};\nx; y", false, ["fn f() {};", "x;"], " y");
    }
}
