use std::{fmt};

use super::loc::{self, Location, Loc, List, Report};
use super::stream::{Stream};
use super::{enums, lexer};
use enums::{Separator, BracketKind as BK, Op, Precedence, OpInfo, ItemWord};
use lexer::{Comment, Atom, Lexeme};

pub const MISSING_ITEM: &'static str = "Expected an item";
pub const MISMATCHED_BRACKET: &'static str = "Mismatched bracket";
pub const MISSING_LEFT: &'static str = "Missing formula before this operator";
pub const MISSING_RIGHT: &'static str = "Missing formula after this operator";
pub const MISSING_OP: &'static str = "Missing operator before this formula";

/// Convenience method for discarding [`Lexeme::Comment`]s.
fn read_non_comment(input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Loc<Lexeme>, loc::Error> {
    loop {
        let l = input.read()?;
        if !matches!(&l.0, Lexeme::Comment(_)) { return Ok(l); }
    }
}

// ----------------------------------------------------------------------------

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(pub T, pub List<Comment>);

impl Doc<Item> {
    /// Parse a [`Item`] preceded by zero or more [`Comment`]s.
    pub fn parse(input: &mut impl Stream<Item=Loc<Lexeme>>)
    -> Result<Option<Self>, loc::Error> {
        let mut docs = Vec::new();
        loop {
            let l = input.read()?;
            match &l.0 {
                Lexeme::Comment(comment) => { docs.push(Loc(comment.clone(), l.1)); },
                _ => { input.unread(l); break; },
            }
        }
        Ok(Item::parse(input)?.map(|ret| Self(ret, docs.into())))
    }
}

impl<T: fmt::Debug> fmt::Debug for Doc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

// ----------------------------------------------------------------------------

/// [`Atom`]s combined using [`Bracket`]s and [`Op`]s.
#[derive(Clone)]
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
    /// Returns a [`Location`] spanning `Self`.
    pub fn loc(&self) -> Location { Location {start: self.loc_start(), end: self.loc_end()} }

    /// Used to compute `self.loc().start`.
    pub fn loc_start(&self) -> usize {
        match self {
            Self::Atom(l) => l.1.start,
            Self::RoundGroup(l) => l.1.start,
            Self::SquareGroup(l) => l.1.start,
            Self::Op(Some(left), _, _) => left.loc_start(),
            Self::Op(None, l, _) => l.1.start,
            Self::RoundCall(left, _) => left.loc_start(),
            Self::SquareCall(left, _) => left.loc_start(),
        }
    }

    /// Used to compute `self.loc().end`.
    pub fn loc_end(&self) -> usize {
        match self {
            Self::Atom(l) => l.1.end,
            Self::RoundGroup(l) => l.1.end,
            Self::SquareGroup(l) => l.1.end,
            Self::Op(_, _, Some(right)) => right.loc_end(),
            Self::Op(_, l, None) => l.1.end,
            Self::RoundCall(_, l) => l.1.end,
            Self::SquareCall(_, l) => l.1.end,
        }
    }

    /// Parse an optional [`Self`] containing operators whose left
    /// [`Precedence`] exceeds `limit`.
    ///
    /// Use `Precedence::MIN` for `limit` to parse a complete `Self`.
    pub fn parse(limit: Precedence, input: &mut impl Stream<Item=Loc<Lexeme>>)
    -> Result<Option<Self>, loc::Error> {
        // Parse an initial [`Self`].
        let l = read_non_comment(input)?;
        let mut ret = match &l.0 {
            Lexeme::Atom(atom) => Self::Atom(Loc(atom.clone(), l.1)),
            Lexeme::Op(op_word) => {
                let OpInfo {op, left, right} = op_word.without_left;
                if let Some(left) = left {
                    if limit >= left {
                        input.unread(l);
                        return Ok(None);
                    }
                    Err(Loc(MISSING_LEFT, l.1))?
                } else {
                    Self::parse_operand(None, Loc(op, l.1), right, input)?
                }
            },
            Lexeme::Open(BK::Round) => Self::RoundGroup(parse_bracket(Loc(BK::Round, l.1), input)?),
            Lexeme::Open(BK::Square) => Self::SquareGroup(parse_bracket(Loc(BK::Square, l.1), input)?),
            _ => {
                input.unread(l);
                return Ok(None);
            },
        };
        // Parse operators whose [`Precedence`] exceeds `limit`, and their
        // operands.
        loop {
            let l = read_non_comment(input)?;
            ret = match &l.0 {
                Lexeme::Atom(_) => { Err(Loc(MISSING_OP, l.1))? },
                Lexeme::Op(op_word) => {
                    let OpInfo {op, left, right} = op_word.with_left;
                    if let Some(left) = left {
                        if limit >= left {
                            input.unread(l);
                            return Ok(Some(ret));
                        }
                        Self::parse_operand(Some(ret), Loc(op, l.1), right, input)?
                    } else {
                        Err(Loc(MISSING_OP, l.1))?
                    }
                },
                Lexeme::Open(BK::Round) => Self::RoundCall(Box::new(ret), parse_bracket(Loc(BK::Round, l.1), input)?),
                Lexeme::Open(BK::Square) => Self::SquareCall(Box::new(ret), parse_bracket(Loc(BK::Square, l.1), input)?),
                _ => {
                    input.unread(l);
                    return Ok(Some(ret));
                },
            };
        }
    }

    /// Given an optional left operand, an operator, and its right
    /// [`Precedence`] (if any) Parse the right operand (if any).
    fn parse_operand(left: Option<Self>, op: Loc<Op>, right: Option<Precedence>, input: &mut impl Stream<Item=Loc<Lexeme>>)
    -> Result<Self, loc::Error> {
        let right = if let Some(right) = right {
            Some(Self::parse(right, input)?.ok_or(Loc(MISSING_RIGHT, op.1))?)
        } else {
            None
        };
        Ok(Self::Op(left.map(Box::new), op, right.map(Box::new)))
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Atom(atom) => atom.fmt(f),
            Self::RoundGroup(bracket) => {
                let mut t = f.debug_tuple("RoundGroup");
                for item in &bracket.0 { t.field(item); }
                t.finish()
            },
            Self::SquareGroup(bracket) => {
                let mut t = f.debug_tuple("SquareGroup");
                for item in &bracket.0 { t.field(item); }
                t.finish()
            },
            Self::Op(left, op, right) => {
                let mut t = f.debug_tuple("Op");
                if let Some(left) = left { t.field(left); }
                t.field(op);
                if let Some(right) = right { t.field(right); }
                t.finish()
            },
            Self::RoundCall(left, bracket) => f.debug_tuple("RoundCall").field(left).field(bracket).finish(),
            Self::SquareCall(left, bracket) => f.debug_tuple("SquareCall").field(left).field(bracket).finish(),
        }
    }
}

// ----------------------------------------------------------------------------

/// The top-level non-terminal in a source file, at the REPL, or inside a
/// bracket.
///
/// `Item`s are generally wrapped in [`Doc`].
#[derive(Clone)]
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
    /// Returns a [`Location`] encompassing `Self`.
    pub fn loc(&self) -> Location {
        match self {
            Self::Separator(separator) => separator.1,
            Self::Eval(expr) => expr.loc(),
            Self::Assign(Some(pattern), _, Some(expr)) => Location {start: pattern.loc_start(), end: expr.loc_end()},
            Self::Assign(Some(pattern), op, None) => Location {start: pattern.loc_start(), end: op.1.end},
            Self::Assign(None, op, Some(expr)) => Location {start: op.1.start, end: expr.loc_end()},
            Self::Assign(None, op, None) => op.1,
            Self::Verb(word, Some(expr)) => Location {start: word.1.start, end: expr.loc_end()},
            Self::Verb(word, None) => word.1,
            Self::Control(word, _expr, block) => Location {start: word.1.start, end: block.1.end},
            Self::Block(block) => block.1,
        }
    }

    /// Parse a [`Self`].
    pub fn parse(input: &mut impl Stream<Item=Loc<Lexeme>>)
    -> Result<Option<Self>, loc::Error> {
        let l = read_non_comment(input)?;
        let ret: Self = match &l.0 {
            Lexeme::Atom(_) | Lexeme::Op(_) | Lexeme::Open(BK::Round) | Lexeme::Open(BK::Square) | Lexeme::Assign(_) => {
                input.unread(l);
                let lhs = Formula::parse(Precedence::MIN, input)?;
                let l = read_non_comment(input)?;
                match &l.0 {
                    Lexeme::Assign(op) => {
                        let op = Loc(*op, l.1);
                        let rhs = Formula::parse(Precedence::MIN, input)?;
                        Self::Assign(lhs, op, rhs)
                    },
                    _ => {
                        input.unread(l);
                        Self::Eval(lhs.expect("We checked the first Lexeme"))
                    },
                }
            },
            Lexeme::Item(word) => {
                let word = Loc(*word, l.1);
                let expr = Formula::parse(Precedence::MIN, input)?;
                let l = read_non_comment(input)?;
                match &l.0 {
                    Lexeme::Open(BK::Curly) => {
                        let block = parse_bracket(Loc(BK::Curly, l.1), input)?;
                        Self::Control(word, expr, block)
                    },
                    _ => {
                        input.unread(l);
                        Self::Verb(word, expr)
                    },
                }
            },
            Lexeme::Open(BK::Curly) => {
                let block = parse_bracket(Loc(BK::Curly, l.1), input)?;
                Self::Block(block)
            },
            Lexeme::Separator(sep) => { Self::Separator(Loc(*sep, l.1)) },
            _ => {
                input.unread(l);
                return Ok(None);
            },
        };
        Ok(Some(ret))
    }
}

impl fmt::Debug for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Self::Separator(sep) => sep.fmt(f),
            Self::Eval(formula) => formula.fmt(f),
            Self::Assign(left, op, right) => {
                let mut t = f.debug_tuple("Assign");
                if let Some(left) = left { t.field(left); }
                t.field(op);
                if let Some(right) = right { t.field(right); }
                t.finish()
            },
            Self::Verb(word, formula) => {
                let mut t = f.debug_tuple("Verb");
                t.field(word);
                if let Some(formula) = formula{ t.field(formula); }
                t.finish()
            },
            Self::Control(word, formula, block) => {
                let mut t = f.debug_tuple("Control");
                t.field(word);
                if let Some(formula) = formula{ t.field(formula); }
                t.field(block);
                t.finish()
            },
            Self::Block(bracket) => {
                let mut t = f.debug_tuple("Block");
                for item in &bracket.0 { t.field(item); }
                t.finish()
            }
        }
    }
}

// ----------------------------------------------------------------------------

/// An open bracket does not match a close bracket.
struct MismatchedBracket {open: Location, close: Location}

impl Report for MismatchedBracket {
    fn report(&self, log: &mut dyn FnMut(&str, Option<Location>)) {
        log(MISMATCHED_BRACKET, Some(self.open));
        log(MISMATCHED_BRACKET, Some(self.close));
    }
}

/// Represents a sequence of [`Item`] inside brackets.
type Bracket = Box<[Doc<Item>]>;

/// Parse a [`Bracket`] starting after the open bracket.
/// - open - the open bracket.
pub fn parse_bracket(open: Loc<BK>, input: &mut impl Stream<Item=Loc<Lexeme>>)
-> Result<Loc<Bracket>, loc::Error> {
    let mut contents = Vec::new();
    loop {
        let l = read_non_comment(input)?;
        match &l.0 {
            Lexeme::Close(kind) => {
                if *kind == open.0 {
                    let loc = Location {start: open.1.start, end: l.1.end};
                    return Ok(Loc(contents.into(), loc));
                } else {
                    Err(MismatchedBracket {open: open.1, close: l.1})?
                }
            },
            _ => {},
        }
        input.unread(l);
	if let Some(item) = Doc::parse(input)? { contents.push(item); }
    }
}
