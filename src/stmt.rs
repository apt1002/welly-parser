use super::{enums, lexer, loc};
use enums::{Op, StmtWord};
use loc::{List};

/// A `T` and its documentation.
#[derive(Debug, Clone, PartialEq)]
pub struct Doc<T>(T, List<lexer::Comment>);

// ----------------------------------------------------------------------------

/// Part of an expression. An expression is a [`List<Expr>`].
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Part of an expression that isn't in brackets.
    Expr(lexer::Expr),

    /// Something enclosed in round brackets.
    Round(Block),

    /// Something enclosed in square brackets.
    Square(Block),
}

// ----------------------------------------------------------------------------

/// A complete statement, or a comma.
// TODO: `Location`s.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// A comma.
    Comma,

    /// `expr;` evaluates `expr`. Used at the REPL, it prints out the value of
    /// the expression.
    ///
    /// In round or square brackets, `expr` is part of a comma-separated list.
    // TODO: When is the semicolon needed?
    Expr(List<Expr>),

    /// `pattern op= expr;` mutates the names in the pattern.
    Assign(List<Expr>, Option<Op>, List<Expr>),

    /// `keyword expr;`
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Verb(StmtWord, List<Expr>),

    /// `keyword expr { ... }`.
    ///
    /// The meaning depends on the keyword. See [`StmtWord`].
    Control(StmtWord, List<Expr>, Block),
}

// ----------------------------------------------------------------------------

type Block = List<Doc<Stmt>>;
