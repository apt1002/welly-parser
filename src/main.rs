use std::{io};
use io::{BufRead, Write};

use welly_parser::{Buffer};

fn main() -> std::io::Result<()> {
    echo(&mut io::stdin().lock(), &mut io::stdout())?;
    Ok(())
}

pub fn echo<R: BufRead, W: Write>(input: &mut R, output: &mut W) -> io::Result<()> {
    let mut buffer = Buffer::default();
    let mut line = String::new();
    while !buffer.is_complete() {
        if buffer.remainder().len() == 0 {
            write!(output, "\nWelly!\n")?;
        }
        output.flush()?;
        if input.read_line(&mut line)? == 0 {
            buffer.complete();
        } else {
            buffer.push_str(&line);
            line.clear();
        }
        while let Some((source, token)) = buffer.try_parse() {
            let loc = token.location();
            write!(output, "Parsed '{}' into {:#?}\n", &source[loc.start..loc.end], token.result())?;
        }
    }
    Ok(())
}
