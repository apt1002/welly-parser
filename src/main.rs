use std::{io};
use io::{BufRead, Write};
use ansi_term::Colour::{Red, Blue};

use welly_parser::{loc, stream, lexer, parser, ast};
use loc::{Location, Loc};
use stream::{Stream, IteratorStream, CharIterator};
use lexer::{Lexer};
use parser::{Doc, Item};
use ast::{Validate, Block};

pub const MISSING_STATEMENT: &'static str = "Expected a statement";

fn main() -> std::io::Result<()> {
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout();
    echo(&mut stdin, &mut stdout)?;
    Ok(())
}

/// Report an error, with an optional [`Location`].
pub fn report(output: &mut impl Write, source: Loc<&str>, msg: &str, loc: Option<Location>) {
    assert_eq!(source.0.len(), source.1.end - source.1.start);
    // Ignore IO errors.
    let _ = writeln!(output, "\n{}: {}",
        Red.paint("Error"),
        msg,
    );
    if let Some(loc) = loc {
        let loc = loc - source.1.start;
        let _ = writeln!(output, "{}{}{}",
            &source.0[..loc.start],
            Red.paint(&source.0[loc.start..loc.end]),
            &source.0[loc.end..],
        );
    }
}

/// Lex, parse, validate and execute `command`.
/// - history_len - the total length in bytes of the command history.
pub fn run(output: &mut impl Write, lexer: &Lexer, command: Loc<&str>)
-> loc::Result<()> {
    // Lex.
    let mut lexemes = Vec::new();
    let mut char_stream = IteratorStream::from(CharIterator::new(command));
    while !char_stream.is_empty() {
        if let Some(l) = lexer.lex(&mut char_stream)? { lexemes.push(l); }
    }
    // Parse.
    let mut items = Vec::new();
    let mut lexeme_stream = IteratorStream::from(lexemes.into_iter());
    while !lexeme_stream.is_empty() {
        let Some(item) = Doc::parse(&mut lexeme_stream)? else {
            // E.g. a `Lexeme::Close`.
            let l = lexeme_stream.read()?;
            Err(Loc(MISSING_STATEMENT, l.1))?
        };
        items.push(item);
    }
    let items: Box<[Doc<Item>]> = items.into();
    // Validate.
    let stmts = Block::validate(&items)?.0;
    // Show.
    for stmt in stmts {
        // Ignore IO errors.
        let stmt_output = format!("{:#?}", stmt);
        let _ = writeln!(output, "{}", Blue.paint(stmt_output));
    }
    Ok(())
}

pub fn echo<R: BufRead, W: Write>(input: &mut R, output: &mut W) -> io::Result<()> {
    let mut history = String::new();
    let mut command = String::new();
    let mut is_complete = false;
    let lexer = Lexer::default();
    while !is_complete {
        if command.is_empty() {
            writeln!(output, "\nWelly!")?;
        }
        output.flush()?;
        if input.read_line(&mut command)? == 0 { is_complete = true; }
        let loc_command = Loc(command.as_str(), Location {start: history.len(), end: history.len() + command.len()});
        match run(output, &lexer, loc_command) {
            Ok(()) => {
                history.push_str(&command);
                command.clear();
            },
            Err(e) => {
                if is_complete || !matches!(e, loc::Error::InsufficientInput) {
                    e.report(|msg, loc| report(output, loc_command, msg, loc));
                    command.clear();
                }
            },
        }
    }
    Ok(())
}
