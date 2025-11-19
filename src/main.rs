use std::{io};
use io::{BufRead, Write};
use ansi_term::Colour::{Red};

use welly_parser::loc::{Loc};
use welly_parser::stream::{IteratorStream, CharIterator};
use welly_parser::lexer::{Lexer};
use welly_parser::stmt::{Doc, parse_doc_stmt};

fn main() -> std::io::Result<()> {
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout();
    echo(&mut stdin, &mut stdout)?;
    Ok(())
}

pub fn report(output: &mut impl Write, source: &str, msg: Loc<&str>) {
    let Loc(msg, loc) = msg;
    // Ignore IO errors.
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

/// Lex, parse, and execute `source_code` starting at `start_pos`.
/// Update `start_pos`.
pub fn run(output: &mut impl Write, lexer: &Lexer, source_code: &str, start_pos: &mut usize)
-> Result<(), Option<Loc<&'static str>>> {
    // Lex.
    let mut lexemes = Vec::new();
    let mut char_stream = IteratorStream::from(CharIterator::new(source_code, *start_pos));
    while let Some(lexeme) = lexer.lex(&mut char_stream)? {
        lexemes.push(lexeme);
    }
    // Parse.
    let mut stmts = Vec::new();
    let mut lexeme_stream = IteratorStream::from(lexemes.into_iter());
    // TODO: Report errors.
    loop {
        match parse_doc_stmt(&mut lexeme_stream) {
            Ok(Doc(stmt, _)) => {
                *start_pos = stmt.loc().end;
                stmts.push(stmt);
            },
            Err(None) => { break; },
            Err(error) => { Err(error)? },
        }
    }
    // let valid_stmts = stmts.into_iter().map(|stmt| stmt::validate(stmt)).collect();
    for stmt in stmts {
        let loc = stmt.loc();
        // Ignore IO errors.
        let _ = writeln!(output, "Parsed '{}' into {:#?}",
            &source_code[loc.start..loc.end],
            stmt,
        );
    }
    Ok(())
}

pub fn echo<R: BufRead, W: Write>(input: &mut R, output: &mut W) -> io::Result<()> {
    let mut source_code = String::new();
    let mut is_complete = false;
    let mut start_pos = 0;
    let lexer = Lexer::default();
    while !is_complete {
        if source_code[start_pos..].trim().is_empty() {
            start_pos = source_code.len();
            writeln!(output, "\nWelly!")?;
        }
        output.flush()?;
        if input.read_line(&mut source_code)? == 0 {
            is_complete = true;
        }
        match run(output, &lexer, &source_code, &mut start_pos) {
            Ok(()) => {},
            Err(None) => {}
            Err(Some(message)) => {
                report(output, &source_code, message);
                start_pos = source_code.len();
            },
        }
    }
    // TODO: Any remamining non-whitespace code is an error.
    Ok(())
}
