use std::{io};
use io::{BufRead, Write};

mod parser;
pub use parser::{Location, Token, TokenIterator, Failure, fail, Context, Parse, Parser};

mod buffer;
pub use buffer::{Buffer};

pub mod escape;
pub mod lexer;
pub mod word;

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
