use std::{io};
use io::{BufRead, Write};
use ansi_term::Colour::{Red};

use welly_parser::loc::{self, Location, Loc};
use welly_parser::stream::{Stream, IteratorStream, CharIterator};
use welly_parser::lexer::{Lexer};
use welly_parser::parser::{Doc};

pub const MISSING_STATEMENT: &'static str = "Expected a statement";

fn main() -> std::io::Result<()> {
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout();
    echo(&mut stdin, &mut stdout)?;
    Ok(())
}

pub fn report(output: &mut impl Write, source: &str, msg: &str, loc: Option<Location>) {
    // Ignore IO errors.
    let _ = writeln!(output, "\n{}: {}",
        Red.paint("Error"),
        msg,
    );
    if let Some(loc) = loc {
        let _ = writeln!(output, "{}{}{}",
            &source[..loc.start],
            Red.paint(&source[loc.start..loc.end]),
            &source[loc.end..],
        );
    }
}

/// Lex, parse, and execute `source_code` starting at `start_pos`.
/// Update `start_pos` if successful.
pub fn run(output: &mut impl Write, lexer: &Lexer, source_code: &str, start_pos: &mut usize)
-> Result<(), loc::Error> {
    // Lex.
    let mut lexemes = Vec::new();
    let mut char_stream = IteratorStream::from(CharIterator::new(source_code, *start_pos));
    while !char_stream.is_empty() {
        if let Some(l) = lexer.lex(&mut char_stream)? { lexemes.push(l); }
    }
    // Parse.
    let mut items = Vec::new();
    let mut lexeme_stream = IteratorStream::from(lexemes.into_iter());
    while !lexeme_stream.is_empty() {
        let Some(Doc(item, _)) = Doc::parse(&mut lexeme_stream)? else {
            let l = lexeme_stream.read()?;
            Err(Loc(MISSING_STATEMENT, l.1))?
        };
        items.push(item);
    }
    // let valid_items = items.into_iter().map(|item| item::validate(item)).collect();
    for item in items {
        let loc = item.loc();
        *start_pos = loc.end;
        // Ignore IO errors.
        let _ = writeln!(output, "Parsed '{}' into {:#?}",
            &source_code[loc.start..loc.end],
            item,
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
            Err(e) => {
                if is_complete || !matches!(e, loc::Error::InsufficientInput) {
                    e.report(|msg, loc| report(output, &source_code, msg, loc));
                    source_code.truncate(start_pos);
                }
            },
        }
    }
    Ok(())
}
