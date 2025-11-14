use std::{io};
use io::{BufRead, Write};
use ansi_term::Colour::{Red};

use welly_parser::loc::{Location};

fn main() -> std::io::Result<()> {
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout();
    echo(&mut stdin, &mut stdout)?;
    Ok(())
}

pub fn report(output: &mut impl Write, source: &str, loc: Location, msg: &str) {
    // Ignore errors.
    let _ = writeln!(output, "\n{}: {}",
        Red.paint("Error"),
        msg,
    );
    let _ = writeln!(output, "{}{}{}",
        &source[..loc.start],
        Red.paint(&source[loc.start..loc.end]),
        &source[loc.end..],
    );
}

pub fn echo<R: BufRead, W: Write>(input: &mut R, output: &mut W) -> io::Result<()> {
    /* Old version.
    let mut buffer = Buffer::default();
    let mut line = String::new();
    while !buffer.is_complete() {
        if buffer.remainder().trim().is_empty() {
            buffer.clear();
            writeln!(output, "\nWelly!")?;
        }
        output.flush()?;
        if input.read_line(&mut line)? == 0 {
            buffer.complete();
        } else {
            buffer.push_str(&line);
            line.clear();
        }
        while let Some((source, token)) = buffer.try_parse() {
            let mut report = |loc: Location, msg: &str| report(output, &*source, loc, msg);
            let loc = token.location();
            match token.result_ref() {
                Ok(tree) => {
                    if let Some(stmt) = tree.downcast_ref::<stmt::Stmt>() {
                        if let Ok(stmt) = ast::Stmt::validate(&mut report, stmt) {
                            let _ = writeln!(output, "Parsed '{}' into {:#?}",
                                &source[loc.start..loc.end],
                                stmt,
                            );
                        }
                    } else {
                        report(loc, "Not a statement");
                    }
                },
                Err(msg) => report(loc, msg),
            }
        }
    }
    */
    Ok(())
}
