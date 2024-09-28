use std::{io};
use io::{BufRead, Write};

mod tree;
pub use tree::{Tree};

mod parser;
pub use parser::{EndOfFile, Location, Token, Stream, Context, Parse, Parser};

mod buffer;
pub use buffer::{Buffer, Characters};

pub mod lexer;
pub mod word;
pub mod bracket;
pub mod expr;
pub mod stmt;

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
