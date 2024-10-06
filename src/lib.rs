use std::{io};
use io::{BufRead, Write};

mod tree;
pub use tree::{Tree, EndOfFile};

mod stream;
pub use stream::{Location, Token, Stream, Characters};

mod parser;
pub use parser::{Context, Parse};

pub mod lexer;
pub mod word;
pub mod bracket;
pub mod expr;
pub mod stmt;

/// The main entry point.
#[derive(Debug)]
pub struct Parser(word::Parser);

impl Default for Parser {
    fn default() -> Self {
        let mut word_parser = word::Parser::default();
        word_parser.add_keywords::<expr::Operator>();
        word_parser.add_keywords::<expr::Keyword>();
        word_parser.add_keywords::<stmt::Keyword>();
        word_parser.add_keywords::<stmt::AssignOp>();
        Self(word_parser)
    }
}

impl Parser {
    /// Returns a [`Stream`] containing [`Stmt`]s, amidst any unparseable junk.
    ///
    /// [`Location`]s are relative to `source`.
    pub fn parse<'a>(&'a self, source: &'a str) -> impl 'a + Stream {
        let stream = Characters::new(source);
        let stream = lexer::Parser.parse_stream(stream);
        let stream = (&self.0).parse_stream(stream);

        /// Parse a [`Stream`] containing [`Brace`]s into [`Round`]s and [`Expr`]s.
        fn round(input: impl Stream) -> impl Stream {
            stmt::Parser.parse_stream(expr::Parser.parse_stream(bracket::Parser::new('(', ')', |contents| {
                let contents = expr::Parser.parse_stream(contents.into_iter()).read_all();
                Box::new(bracket::Round(contents))
            }, input)))
        }

        /// Parse a [`Stream`] into [`Brace`]s, [`Round`]s and [`Expr`]s.
        fn brace(input: impl Stream) -> impl Stream {
            round(bracket::Parser::new('{', '}', |contents| {
                let contents = round(contents.into_iter()).read_all();
                Box::new(bracket::Brace(contents))
            }, input))
        }

        brace(stream)
    }
}

mod buffer;
pub use buffer::{Buffer};

pub fn echo<R: BufRead, W: Write>(input: &mut R, output: &mut W) -> io::Result<()> {
    let mut line = String::new();
    loop {
        if input.read_line(&mut line)? == 0 { return Ok(()); }
        write!(output, "{}", &line)?;
        line.clear();
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {}
