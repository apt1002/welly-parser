use std::{fmt};

use super::{enums, loc, Validate, Name, Selector, Expr};
use enums::{BracketKind, Op};
use loc::{Loc, Locate};

pub const BAD_PATTERN: &'static str = "This expression is not assignable";

// ----------------------------------------------------------------------------

/// Indicates whether a value is mutable and/or borrowed.
#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum Mode {
    /// A mutable value (not shared).
    Mut,

    /// A reference-counted value (not mutable).
    Ref,

    /// A loan of a mutable value.
    MutLoan,

    /// A loan of a reference-counted value.
    RefLoan,

    /// A loan of a value of unknown `Mode`.
    Loan,
}

impl Mode {
    /// Computes the `Mode` that results from sharing something of mode `self`.
    fn share(self) -> Self {
        match self {
            Self::Mut | Self::Ref | Self::RefLoan => Self::Ref,
            Self::MutLoan | Self::Loan => Self::Loan,
        }
    }

    /// Computes the `Mode` that results from lending something of mode `self`.
    fn lend(self) -> Self {
        match self {
            Self::Mut | Self::MutLoan => Self::MutLoan,
            Self::Ref | Self::RefLoan => Self::RefLoan,
            Self::Loan => Self::Loan,
        }
    }
}

// ----------------------------------------------------------------------------

/// Unpack a value and bind the parts to [`Name`]s.
///
/// It is a compile-time error if the structure of the value does not match the
/// structure of the pattern.
#[derive(Clone)]
pub enum Pattern {
    /// Bind the value to a `Name`.
    Name(Mode, Loc<Name>),

    /// Unpack a tuple's fields.
    Group(Loc<Box<Pattern>>),

    /// Unpack a tuple's fields.
    Tuple(Loc<Box<[Pattern]>>),

    /// `pattern: type` casts the value to `type` then unpacks it.
    Cast(Box<Pattern>, Box<Expr>),

    /// `expr.name` sets field `name` of `expr` to the value.
    Dot(Box<Expr>, Loc<Selector>),
}

impl Pattern {
    /// Check that `expr` is a `Pattern`.
    pub fn from_expr(expr: Expr) -> loc::Result<Self> { Self::from_expr_mode(expr, Mode::Mut) }

    /// The recursive part of `from_expr`.
    ///
    /// - mode - the mode that will be applied to any names in `expr`.
    fn from_expr_mode(expr: Expr, mode: Mode) -> loc::Result<Self> {
        let ret = match expr {
            Expr::Name(name) => Self::Name(mode, name),
            Expr::Group(BracketKind::Round, expr) =>
                Self::Group(Loc(Box::new(Self::from_expr_mode(*expr.0, mode)?), expr.1)),
            Expr::Tuple(BracketKind::Round, exprs) => {
                let mut patterns = Vec::new();
                for expr in exprs.0 { patterns.push(Self::from_expr_mode(expr, mode)?); }
                Self::Tuple(Loc(patterns.into(), exprs.1))
            },
            Expr::Op(None, Loc(Op::Share, _), Some(expr)) => Self::from_expr_mode(*expr, mode.share())?,
            Expr::Op(None, Loc(Op::Lend, _), Some(expr)) => Self::from_expr_mode(*expr, mode.lend())?,
            Expr::Op(Some(expr), Loc(Op::Cast, _), Some(type_)) => {
                Self::Cast(Box::new(Self::from_expr_mode(*expr, mode)?), type_)
            },
            Expr::Dot(expr, selector) => Self::Dot(expr, selector),
            expr => { Err(Loc(BAD_PATTERN, expr.loc()))? },
        };
        Ok(ret)
    }

    /// Tests whether `self` is `_`.
    pub fn is_underscore(&self) -> bool {
        match self {
            Self::Name(_, name) => "_" == &*name.0,
            _ => false,
        }
    }
}

impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Name(mode, name) => write!(f, "{:?} {:?}", mode, name),
            Self::Group(pattern) => f.debug_tuple("Group").field(&pattern.0).finish(),
            Self::Tuple(patterns) => {
                let mut t = f.debug_tuple("Tuple");
                for pattern in &patterns.0 { t.field(pattern); }
                t.finish()
            },
            Self::Cast(pattern, expr) => f.debug_tuple("Cast").field(pattern).field(expr).finish(),
            Self::Dot(expr, selector) => f.debug_tuple("Dot").field(expr).field(selector).finish(),
        }
    }
}

impl Locate for Pattern {
    fn loc_start(&self) -> usize {
        match self {
            Self::Name(_, name) => name.loc_start(),
            Self::Group(pattern) => pattern.loc_start(),
            Self::Tuple(tuple) => tuple.loc_start(),
            Self::Cast(pattern, _) => pattern.loc_start(),
            Self::Dot(expr, _) => expr.loc_start(),
        }
    }

    fn loc_end(&self) -> usize {
        match self {
            Self::Name(_, name) => name.loc_end(),
            Self::Group(pattern) => pattern.loc_end(),
            Self::Tuple(tuple) => tuple.loc_end(),
            Self::Cast(_, type_) => type_.loc_end(),
            Self::Dot(_, selector) => selector.loc_end(),
        }
    }
}

impl<T> Validate<T> for Pattern where Expr: Validate<T> {
    fn validate(tree: &T) -> loc::Result<Self> { Ok(Self::from_expr(Expr::validate(tree)?)?) }
}
