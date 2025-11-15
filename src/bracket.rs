use super::{enums, lexer, loc};
use enums::{BracketKind};
use loc::{List};

/// The output type of the bracket matcher.
#[derive(Debug, Clone)]
pub enum Item {
    /// A comment.
    Comment(lexer::Comment),

    /// Part of an expression.
    Expr(lexer::Expr),

    /// Part of a statement.
    Stmt(lexer::Stmt),

    /// A sequence of `Token`s enclosed in brackets.
    Bracket(BracketKind, List<Item>),
}

// ----------------------------------------------------------------------------

