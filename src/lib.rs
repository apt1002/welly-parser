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

/// Returns a parser that replaces all Welly keywords with their parse trees.
pub fn word_parser() -> word::Parser {
    let mut ret = word::Parser::default();
    ret.add_keywords::<expr::Operator>();
    ret.add_keywords::<expr::Keyword>();
    ret.add_keywords::<stmt::Keyword>();
    ret.add_keywords::<stmt::AssignOp>();
    ret
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
