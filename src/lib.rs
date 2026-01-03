use welly_main::{self as wm, Location, Loc, Locate, Report};

pub mod enums;
pub mod stream;
pub mod lexer;
pub mod parser;
pub mod ast;

pub const MISSING_STATEMENT: &'static str = "Expected a statement";

// ----------------------------------------------------------------------------

use stream::{Stream, IteratorStream, CharIterator};
use lexer::{Lexer};
use parser::{Doc};
use ast::{Validate, Stmt, Block};

/// Attempt to lex, parse and validate `command`.
pub fn parse(lexer: &Lexer, command: Loc<&str>) -> wm::Result<Box<[Stmt]>> {
    // Lex.
    let mut char_stream = IteratorStream::from(CharIterator::new(command));
    let mut lexemes = Vec::new();
    while !char_stream.is_empty() {
        if let Some(l) = lexer.lex(&mut char_stream)? { lexemes.push(l); }
    }
    // Parse.
    let mut lexeme_stream = IteratorStream::from(lexemes.into_iter());
    let mut items = Vec::new();
    while !lexeme_stream.is_empty() {
        let Some(item) = Doc::parse(&mut lexeme_stream)? else {
            // E.g. a `Lexeme::Close`.
            let l = lexeme_stream.read()?;
            Err(Loc(MISSING_STATEMENT, l.1))?
        };
        items.push(item);
    }
    // Validate.
    Ok(Block::validate(&*items)?.0)
}
