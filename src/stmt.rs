use std::{fmt};

use super::{enums, lexer, loc};
use enums::{Separator, Op, StmtWord};
use loc::{Loc, List};

/// A `T` and its documentation.
#[derive(Clone)]
pub struct Doc<T>(T, List<lexer::Comment>);

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

// ----------------------------------------------------------------------------

/// Represents a sequence of statements inside curly brackets.
type Block = Loc<List<Doc<Stmt>>>;
