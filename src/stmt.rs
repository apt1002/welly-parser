use std::{fmt};

use super::loc::{Location, Loc, List};
use super::stream::{Stream, IteratorStream, CharIterator};
use super::{enums, lexer};
use enums::{Separator, BracketKind, Op, StmtWord};
use lexer::{Lexeme};

pub const UNMATCHED_BRACKET: &'static str = "Unmatched bracket";
pub const MISMATCHED_BRACKET: &'static str = "Mismatched bracket";

// ----------------------------------------------------------------------------

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(pub T, pub List<lexer::Comment>);

impl<T: fmt::Debug> fmt::Debug for Doc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

// ----------------------------------------------------------------------------

/// Part of an expression. An expression is a [`List<Expr>`].
#[derive(Debug, Clone)]
pub enum Expr {
    /// Part of an expression that isn't in brackets.
    Expr(lexer::Expr),

    /// Something enclosed in round brackets.
    Round(Block),

    /// Something enclosed in square brackets.
    Square(Block),
}

/// A comma.
struct Comma;

/// A comma-separated list of expressions possibly with a trailing comma.
pub struct ExprList {
    with_commas: Box<[(List<Expr>, Loc<Comma>)]>,
    without_comma: Option<List<Expr>>,
}

// ----------------------------------------------------------------------------

/// A complete statement, or a [`Separator`].
///
/// The output type of the parser is [`Doc<Stmt>`].
#[derive(Debug, Clone)]
pub enum Stmt {
    /// A comma or semicolon.
    Separator(Loc<Separator>),

    /// Any expression is a statement. Used at the REPL, it prints out the
    /// value of the expression.
    Expr(List<Expr>),

    /// `pattern op= expr;` mutates the names in the pattern.
    Assign(List<Expr>, Loc<Option<Op>>, List<Expr>),

    /// `keyword expr;`
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Verb(Loc<StmtWord>, List<Expr>),

    /// `keyword expr { ... }`.
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Control(Loc<StmtWord>, List<Expr>, Block),
}

impl Stmt {
    /// Returns a [`Location`] encompassing the entire `Stmt`.
    pub fn loc(stmt: &Stmt) -> Location {
        match stmt {
            Stmt::Separator(separator) => separator.1,
            Stmt::Expr(expr) => expr.loc().expect("Empty List<Expr>"),
            Stmt::Assign(pattern, op, expr) => Location {
                start: pattern.loc().unwrap_or(op.1).start,
                end: expr.loc().unwrap_or(op.1).end,
            },
            Stmt::Verb(word, expr) => Location {
                start: word.1.start,
                end: expr.loc().unwrap_or(word.1).end,
            },
            Stmt::Control(word, expr, block) => Location {
                start: word.1.start,
                end: block.1.end,
            },
        }
    }
}

/// Represents a sequence of statements inside brackets.
type Block = Loc<Box<[Doc<Stmt>]>>;

// ----------------------------------------------------------------------------

type StmtError = &'static str;

pub fn parse_doc_stmt(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Doc<Stmt>, Option<Loc<StmtError>>> {
    let mut docs = Vec::new();
    loop {
        let Some(l) = input.read() else { Err(None)? };
        match &l.0 {
            Lexeme::Comment(comment) => { docs.push(Loc(comment.clone(), l.1)); },
            _ => { input.unread(l); break; },
        }
    }
    Ok(Doc(parse_stmt(input)?, docs.into()))
}

pub fn parse_stmt(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Stmt, Option<Loc<StmtError>>> {
    todo!()
}

pub fn parse_block(open: Location, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Block, Option<Loc<StmtError>>> {
    let mut contents = Vec::new();
    loop {
        let Some(l) = input.read() else { Err(Loc(UNMATCHED_BRACKET, open))? };
        match &l.0 {
            Lexeme::Close(kind) => {
                if *kind == BracketKind::Curly {
                    let loc = Location {start: open.start, end: l.1.end};
                    return Ok(Loc(contents.into(), loc));
                } else {
                    // TODO: Report both mismatched brackets.
                    Err(Loc(MISMATCHED_BRACKET, l.1))?
                }
            },
            _ => {},
        }
        input.unread(l);
        contents.push(parse_doc_stmt(input)?);
    }
}

pub fn parse_expr(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<List<Expr>, Option<Loc<StmtError>>> {
    todo!()
}

pub fn parse_expr_list(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<ExprList, Option<Loc<StmtError>>> {
    todo!()
}

#[derive(Default)]
pub struct Parser(lexer::Lexer);

impl Parser {
    pub fn parse(&self, source_code: &str, start_pos: usize)
    -> Result<Doc<Stmt>, Option<Loc<StmtError>>> {
        let char_stream = IteratorStream::from(CharIterator::new(source_code, start_pos));
        let lexeme_stream = IteratorStream::from(self.0.parse_all(char_stream));
        parse_doc_stmt(&mut lexeme_stream)
    }
}
