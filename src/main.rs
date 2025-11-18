use std::{io};
use io::{BufRead, Write};
use ansi_term::Colour::{Red};

use welly_parser::loc::{Location};
use welly_parser::stmt::{parse};

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
    let mut source_code = String::new();
    let mut is_complete = false;
    let mut start_from = 0;
    while !is_complete {
        if source_code[start_from..].trim().is_empty() {
            start_from = source_code.len();
            writeln!(output, "\nWelly!")?;
        }
        output.flush()?;
        if input.read_line(&mut source_code)? == 0 {
            is_complete = true;
        }
        let mut stmts = Vec::new();
        // TODO: Report errors.
        while let Some(stmt) = stmt::parse(source_code, start_from) {
            stmts.push(stmt);
            start_from = stmt.0.loc().end;
        }
        // TODO: Report errors.
        // let valid_stmts = stmts.into_iter().map(|stmt| stmt::validate(stmt)).collect();
        for stmt in stmts {
            let loc = stmt.0.loc();
            writeln!(output, "Parsed '{}' into {:#?}",
                &source_code[loc.start..loc.end],
                stmt,
            )?;
        }
    }
    Ok(())
}
