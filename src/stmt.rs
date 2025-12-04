use std::{fmt};

use super::loc::{Location, Loc, List};
use super::stream::{Stream};
use super::{enums, lexer};
use enums::{Separator, BracketKind, Op, OpWord, StmtWord};
use lexer::{Comment, Atom, Lexeme};

pub const MISSING_STMT: &'static str = "Expected a statement";
pub const MISMATCHED_BRACKET: &'static str = "Mismatched bracket";

// ----------------------------------------------------------------------------

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(pub T, pub List<Comment>);

impl<T: fmt::Debug> fmt::Debug for Doc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

// ----------------------------------------------------------------------------

/// Part of an expression. An expression is a [`List<Expr>`].
#[derive(Debug, Clone)]
pub enum Expr {
    /// A lexeme that is an expression on its own.
    Atom(Atom),

    /// An arithmetic operator or keyword constant.
    Op(OpWord),

    /// Something enclosed in round brackets.
    Round(Bracket),

    /// Something enclosed in square brackets.
    Square(Bracket),
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
    Eval(List<Expr>),

    /// `pattern op= expr;` mutates the names in the pattern.
    Assign(List<Expr>, Loc<Option<Op>>, List<Expr>),

    /// `keyword expr`
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Verb(Loc<StmtWord>, List<Expr>),

    /// `keyword expr { ... }`.
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Control(Loc<StmtWord>, List<Expr>, Loc<Bracket>),
}

impl Stmt {
    /// Returns a [`Location`] encompassing the entire `Stmt`.
    pub fn loc(&self) -> Location {
        match self {
            Stmt::Separator(separator) => separator.1,
            Stmt::Eval(expr) => expr.loc().expect("Empty List<Expr>"),
            Stmt::Assign(pattern, op, expr) => Location {
                start: pattern.loc().unwrap_or(op.1).start,
                end: expr.loc().unwrap_or(op.1).end,
            },
            Stmt::Verb(word, expr) => Location {
                start: word.1.start,
                end: expr.loc().unwrap_or(word.1).end,
            },
            Stmt::Control(word, _expr, block) => Location {
                start: word.1.start,
                end: block.1.end,
            },
        }
    }
}

/// Represents a sequence of [`Stmt`] inside brackets.
type Bracket = Box<[Doc<Stmt>]>;

// ----------------------------------------------------------------------------

type StmtError = &'static str;

/// Parse a [`Stmt`] preceded by zero or more [`Comment`]s.
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

/// Parse a [`Stmt`].
pub fn parse_stmt(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Stmt, Option<Loc<StmtError>>> {
    let Some(l) = input.read() else { Err(None)? };
    Ok(match &l.0 {
        Lexeme::Atom(_) | Lexeme::Op(_) | Lexeme::Open(BracketKind::Round) | Lexeme::Open(BracketKind::Square) => {
            input.unread(l);
            let lhs = parse_expr(input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Assign(op) => {
                    let op = Loc(*op, l.1);
                    let rhs = parse_expr(input)?;
                    Stmt::Assign(lhs, op, rhs)
                },
                _ => {
                    input.unread(l);
                    Stmt::Eval(lhs)
                },
            }
        },
        Lexeme::Stmt(word) => {
            let word = Loc(*word, l.1);
            let expr = parse_expr(input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Open(BracketKind::Curly) => {
                    let block = parse_bracket(Loc(BracketKind::Curly, l.1), input)?;
                    Stmt::Control(word, expr, block)
                },
                _ => {
                    input.unread(l);
                    Stmt::Verb(word, expr)
                },
            }
        },
        Lexeme::Separator(sep) => { Stmt::Separator(Loc(*sep, l.1)) },
        _ => { Err(Loc(MISSING_STMT, l.1))? },
    })
}

/// Parse a [`List<Expr>`] (representing a single `expr`, if non-empty).
pub fn parse_expr(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<List<Expr>, Option<Loc<StmtError>>> {
    let mut exprs = Vec::new();
    loop {
        let Some(l) = input.read() else { Err(None)? };
        exprs.push(match &l.0 {
            Lexeme::Atom(atom) => {
                Loc(Expr::Atom(atom.clone()), l.1)
            },
            Lexeme::Op(op) => {
                Loc(Expr::Op(*op), l.1)
            },
            Lexeme::Open(BracketKind::Round) => {
                parse_bracket(Loc(BracketKind::Round, l.1), input)?.map(Expr::Round)
            },
            Lexeme::Open(BracketKind::Square) => {
                parse_bracket(Loc(BracketKind::Square, l.1), input)?.map(Expr::Square)
            },
            _ => { input.unread(l); break; },
        });
    }
    Ok(List::from(exprs))
}

/// Parse a [`Bracket`] starting after the open bracket.
/// - open - the open bracket.
pub fn parse_bracket(open: Loc<BracketKind>, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Loc<Bracket>, Option<Loc<StmtError>>> {
    let mut contents = Vec::new();
    loop {
        let Some(l) = input.read() else { Err(None)? };
        match &l.0 {
            Lexeme::Close(kind) => {
                if *kind == open.0 {
                    let loc = Location {start: open.1.start, end: l.1.end};
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
