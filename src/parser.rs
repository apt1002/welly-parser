use std::{fmt};

use super::loc::{Location, Loc, List};
use super::stream::{Stream};
use super::{enums, lexer};
use enums::{Separator, BracketKind, Op, OpWord, ItemWord};
use lexer::{Comment, Atom, Lexeme};

pub const MISSING_ITEM: &'static str = "Expected an item";
pub const MISMATCHED_BRACKET: &'static str = "Mismatched bracket";

// ----------------------------------------------------------------------------

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(pub T, pub List<Comment>);

impl<T: fmt::Debug> fmt::Debug for Doc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

// ----------------------------------------------------------------------------

/// Part of a [`Formula`].
#[derive(Debug, Clone)]
pub enum Noun {
    /// A lexeme that is an expression on its own.
    Atom(Atom),

    /// An arithmetic operator or keyword constant.
    Op(OpWord),

    /// Something enclosed in round brackets.
    Round(Bracket),

    /// Something enclosed in square brackets.
    Square(Bracket),
}

/// A maximal string of [`Noun`]s.
type Formula = List<Noun>;

// ----------------------------------------------------------------------------

/// The top-level non-terminal in a source file, at the REPL, or inside a
/// bracket is [`Doc<Item>`].
#[derive(Debug, Clone)]
pub enum Item {
    /// A comma or semicolon.
    Separator(Loc<Separator>),

    /// Any [`Formula`] is an `Item`.
    Eval(Formula),

    /// `pattern op= expr;` mutates the names in the pattern.
    Assign(Formula, Loc<Option<Op>>, Formula),

    /// `keyword expr`
    ///
    /// The meaning depends on the keyword. See [`ItemWord`].
    Verb(Loc<ItemWord>, Formula),

    /// `keyword expr { ... }`.
    ///
    /// The meaning depends on the keyword. See [`ItemWord`].
    Control(Loc<ItemWord>, Formula, Loc<Bracket>),
}

impl Item {
    /// Returns a [`Location`] encompassing the entire `Item`.
    pub fn loc(&self) -> Location {
        match self {
            Item::Separator(separator) => separator.1,
            Item::Eval(expr) => expr.loc().expect("Empty Formula"),
            Item::Assign(pattern, op, expr) => Location {
                start: pattern.loc().unwrap_or(op.1).start,
                end: expr.loc().unwrap_or(op.1).end,
            },
            Item::Verb(word, expr) => Location {
                start: word.1.start,
                end: expr.loc().unwrap_or(word.1).end,
            },
            Item::Control(word, _expr, block) => Location {
                start: word.1.start,
                end: block.1.end,
            },
        }
    }
}

/// Represents a sequence of [`Item`] inside brackets.
type Bracket = Box<[Doc<Item>]>;

// ----------------------------------------------------------------------------

type ItemError = &'static str;

/// Parse an [`Item`] preceded by zero or more [`Comment`]s.
pub fn parse_doc_item(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Doc<Item>, Option<Loc<ItemError>>> {
    let mut docs = Vec::new();
    loop {
        let Some(l) = input.read() else { Err(None)? };
        match &l.0 {
            Lexeme::Comment(comment) => { docs.push(Loc(comment.clone(), l.1)); },
            _ => { input.unread(l); break; },
        }
    }
    Ok(Doc(parse_item(input)?, docs.into()))
}

/// Parse an [`Item`].
pub fn parse_item(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Item, Option<Loc<ItemError>>> {
    let Some(l) = input.read() else { Err(None)? };
    Ok(match &l.0 {
        Lexeme::Atom(_) | Lexeme::Op(_) | Lexeme::Open(BracketKind::Round) | Lexeme::Open(BracketKind::Square) => {
            input.unread(l);
            let lhs = parse_formula(input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Assign(op) => {
                    let op = Loc(*op, l.1);
                    let rhs = parse_formula(input)?;
                    Item::Assign(lhs, op, rhs)
                },
                _ => {
                    input.unread(l);
                    Item::Eval(lhs)
                },
            }
        },
        Lexeme::Item(word) => {
            let word = Loc(*word, l.1);
            let expr = parse_formula(input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Open(BracketKind::Curly) => {
                    let block = parse_bracket(Loc(BracketKind::Curly, l.1), input)?;
                    Item::Control(word, expr, block)
                },
                _ => {
                    input.unread(l);
                    Item::Verb(word, expr)
                },
            }
        },
        Lexeme::Assign(op) => {
            // Guess that `lhs` is missing.
            let lhs = List::from([]);
            let op = Loc(*op, l.1);
            let rhs = parse_formula(input)?;
            Item::Assign(lhs, op, rhs)
        },
        Lexeme::Separator(sep) => { Item::Separator(Loc(*sep, l.1)) },
        _ => { Err(Loc(MISSING_ITEM, l.1))? },
    })
}

/// Parse a possibly-empty [`Formula`].
pub fn parse_formula(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Formula, Option<Loc<ItemError>>> {
    let mut nouns = Vec::new();
    while let Some(noun) = parse_noun(input)? { nouns.push(noun); }
    Ok(List::from(nouns))
}

/// Parse a [`Noun`] if possible.
pub fn parse_noun(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Option<Loc<Noun>>, Option<Loc<ItemError>>> {
    let Some(l) = input.read() else { Err(None)? };
    Ok(Some(match &l.0 {
        Lexeme::Atom(atom) => {
            Loc(Noun::Atom(atom.clone()), l.1)
        },
        Lexeme::Op(op) => {
            Loc(Noun::Op(*op), l.1)
        },
        Lexeme::Open(BracketKind::Round) => {
            parse_bracket(Loc(BracketKind::Round, l.1), input)?.map(Noun::Round)
        },
        Lexeme::Open(BracketKind::Square) => {
            parse_bracket(Loc(BracketKind::Square, l.1), input)?.map(Noun::Square)
        },
        _ => {
            input.unread(l);
            return Ok(None);
        },
    }))
}

/// Parse a [`Bracket`] starting after the open bracket.
/// - open - the open bracket.
pub fn parse_bracket(open: Loc<BracketKind>, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Loc<Bracket>, Option<Loc<ItemError>>> {
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
        contents.push(parse_doc_item(input)?);
    }
}
