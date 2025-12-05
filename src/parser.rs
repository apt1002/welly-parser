use std::{fmt};

use super::loc::{Location, Loc, List};
use super::stream::{Stream};
use super::{enums, lexer};
use enums::{Separator, BracketKind as BK, Op, Precedence, OpInfo, ItemWord};
use lexer::{Comment, Atom, Lexeme};

pub const MISSING_ITEM: &'static str = "Expected an item";
pub const MISMATCHED_BRACKET: &'static str = "Mismatched bracket";
pub const MISSING_LEFT: &'static str = "Missing formula before this operator";
pub const MISSING_RIGHT: &'static str = "Missing formula after this operator";
pub const MISSING_OP: &'static str = "Missing operator before this formula";

// ----------------------------------------------------------------------------

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(pub T, pub List<Comment>);

impl<T: fmt::Debug> fmt::Debug for Doc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

// ----------------------------------------------------------------------------

/// [`Atom`]s combined using [`Bracket`]s and [`Op`]s.
#[derive(Debug, Clone)]
pub enum Formula {
    /// A lexeme that is an expression on its own.
    Atom(Loc<Atom>),

    /// Something enclosed in round brackets.
    RoundGroup(Loc<Bracket>),

    /// Something enclosed in square brackets.
    SquareGroup(Loc<Bracket>),

    /// An arithmetic operator applied to up to two arguments.
    Op(Option<Box<Formula>>, Loc<Op>, Option<Box<Formula>>),

    /// A `Formula` followed by round brackets.
    RoundCall(Box<Formula>, Loc<Bracket>),

    /// A `Formula` followed by square brackets.
    SquareCall(Box<Formula>, Loc<Bracket>),
}

impl Formula {
    /// Returns a [`Location`] spanning this whole `Formula`.
    pub fn loc(&self) -> Location { Location {start: self.loc_start(), end: self.loc_end()} }

    /// Used to compute `self.loc().start`.
    pub fn loc_start(&self) -> usize {
        match self {
            Formula::Atom(l) => l.1.start,
            Formula::RoundGroup(l) => l.1.start,
            Formula::SquareGroup(l) => l.1.start,
            Formula::Op(Some(left), _, _) => left.loc_start(),
            Formula::Op(None, l, _) => l.1.start,
            Formula::RoundCall(left, _) => left.loc_start(),
            Formula::SquareCall(left, _) => left.loc_start(),
        }
    }

    /// Used to compute `self.loc().end`.
    pub fn loc_end(&self) -> usize {
        match self {
            Formula::Atom(l) => l.1.end,
            Formula::RoundGroup(l) => l.1.end,
            Formula::SquareGroup(l) => l.1.end,
            Formula::Op(_, _, Some(right)) => right.loc_end(),
            Formula::Op(_, l, None) => l.1.end,
            Formula::RoundCall(_, l) => l.1.end,
            Formula::SquareCall(_, l) => l.1.end,
        }
    }
}

// ----------------------------------------------------------------------------

/// The top-level non-terminal in a source file, at the REPL, or inside a
/// bracket.
///
/// `Item`s are generally wrapped in [`Doc`].
#[derive(Debug, Clone)]
pub enum Item {
    /// A comma or semicolon.
    Separator(Loc<Separator>),

    /// Any [`Formula`] is an `Item`.
    Eval(Formula),

    /// `pattern op= expr;` mutates the names in the pattern.
    Assign(Option<Formula>, Loc<Option<Op>>, Option<Formula>),

    /// `keyword expr`
    ///
    /// The meaning depends on the keyword. See [`ItemWord`].
    Verb(Loc<ItemWord>, Option<Formula>),

    /// `keyword expr { ... }`.
    ///
    /// The meaning depends on the keyword. See [`ItemWord`].
    Control(Loc<ItemWord>, Option<Formula>, Loc<Bracket>),

    /// Something enclosed in curly brackets.
    Block(Loc<Bracket>)
}

impl Item {
    /// Returns a [`Location`] encompassing the entire `Item`.
    pub fn loc(&self) -> Location {
        match self {
            Item::Separator(separator) => separator.1,
            Item::Eval(expr) => expr.loc(),
            Item::Assign(Some(pattern), _, Some(expr)) => Location {start: pattern.loc_start(), end: expr.loc_end()},
            Item::Assign(Some(pattern), op, None) => Location {start: pattern.loc_start(), end: op.1.end},
            Item::Assign(None, op, Some(expr)) => Location {start: op.1.start, end: expr.loc_end()},
            Item::Assign(None, op, None) => op.1,
            Item::Verb(word, Some(expr)) => Location {start: word.1.start, end: expr.loc_end()},
            Item::Verb(word, None) => word.1,
            Item::Control(word, _expr, block) => Location {start: word.1.start, end: block.1.end},
            Item::Block(block) => block.1,
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
        Lexeme::Atom(_) | Lexeme::Op(_) | Lexeme::Open(BK::Round) | Lexeme::Open(BK::Square) | Lexeme::Assign(_) => {
            input.unread(l);
            let lhs = parse_formula(Precedence::MIN, input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Assign(op) => {
                    let op = Loc(*op, l.1);
                    let rhs = parse_formula(Precedence::MIN, input)?;
                    Item::Assign(lhs, op, rhs)
                },
                _ => {
                    input.unread(l);
                    Item::Eval(lhs.expect("We checked the first Lexeme"))
                },
            }
        },
        Lexeme::Item(word) => {
            let word = Loc(*word, l.1);
            let expr = parse_formula(Precedence::MIN, input)?;
            let Some(l) = input.read() else { Err(None)? };
            match &l.0 {
                Lexeme::Open(BK::Curly) => {
                    let block = parse_bracket(Loc(BK::Curly, l.1), input)?;
                    Item::Control(word, expr, block)
                },
                _ => {
                    input.unread(l);
                    Item::Verb(word, expr)
                },
            }
        },
        Lexeme::Open(BK::Curly) => {
            let block = parse_bracket(Loc(BK::Curly, l.1), input)?;
            Item::Block(block)
        },
        Lexeme::Separator(sep) => { Item::Separator(Loc(*sep, l.1)) },
        _ => { Err(Loc(MISSING_ITEM, l.1))? },
    })
}

/// Parse a [`Formula`] containing operators whose left [`Precedence`] exceeds
/// `limit`. Use `Precedence::MIN` for `limit` to parse a complete `Formula`.
fn parse_formula(limit: Precedence, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Option<Formula>, Option<Loc<ItemError>>> {
    let Some(l) = input.read() else { Err(None)? };
    let formula = match &l.0 {
        Lexeme::Atom(atom) => Formula::Atom(Loc(atom.clone(), l.1)),
        Lexeme::Op(op_word) => {
            let OpInfo {op, left, right} = op_word.without_left;
            if let Some(left) = left {
                if limit < left { Err(Loc(MISSING_LEFT, l.1))? }
                input.unread(l);
                return Ok(None);
            }
            parse_operand(None, Loc(op, l.1), right, input)?
        },
        Lexeme::Open(BK::Round) => Formula::RoundGroup(parse_bracket(Loc(BK::Round, l.1), input)?),
        Lexeme::Open(BK::Square) => Formula::SquareGroup(parse_bracket(Loc(BK::Square, l.1), input)?),
        _ => {
            input.unread(l);
            return Ok(None);
        },
    };
    Ok(Some(parse_operator(formula, limit, input)?))
}

/// Given a left operand, parse operators whose [`Precedence`] exceeds `limit`,
/// and their operands.
fn parse_operator(formula: Formula, limit: Precedence, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Formula, Option<Loc<ItemError>>> {
    let Some(l) = input.read() else { Err(None)? };
    let formula = match &l.0 {
        Lexeme::Atom(_) => { Err(Loc(MISSING_OP, l.1))? },
        Lexeme::Op(op_word) => {
            let OpInfo {op, left, right} = op_word.with_left;
            let Some(left) = left else { Err(Loc(MISSING_OP, l.1))? };
            if limit >= left {
                input.unread(l);
                return Ok(formula);
            }
            parse_operand(Some(formula), Loc(op, l.1), right, input)?
        },
        Lexeme::Open(BK::Round) => Formula::RoundCall(Box::new(formula), parse_bracket(Loc(BK::Round, l.1), input)?),
        Lexeme::Open(BK::Square) => Formula::SquareCall(Box::new(formula), parse_bracket(Loc(BK::Square, l.1), input)?),
        _ => {
            input.unread(l);
            return Ok(formula);
        },
    };
    parse_operator(formula, limit, input)
}

/// Given a left operand, an operator, and its right [`Precedence`] (if any),
/// Parse the right operand (if any).
fn parse_operand(left: Option<Formula>, op: Loc<Op>, right: Option<Precedence>, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Formula, Option<Loc<ItemError>>> {
    let right = if let Some(right) = right {
        Some(parse_formula(right, input)?.ok_or(Loc(MISSING_RIGHT, op.1))?)
    } else {
        None
    };
    Ok(Formula::Op(left.map(Box::new), op, right.map(Box::new)))
}

/// Parse a [`Bracket`] starting after the open bracket.
/// - open - the open bracket.
pub fn parse_bracket(open: Loc<BK>, input: &mut impl Stream<Item=Loc<Lexeme>>)
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
