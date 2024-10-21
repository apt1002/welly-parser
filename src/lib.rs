mod tree;
pub use tree::{Tree, EndOfFile};

mod stream;
pub use stream::{Location, Loc, Token, Stream, Characters};

mod parser;
pub use parser::{Context, Parse};

pub mod lexer;
pub mod word;
pub mod bracket;
pub mod expr;
pub mod stmt;

mod buffer;
pub use buffer::{Buffer};

/// Re-exports all the Welly [`Parse`] implementations and [`Brackets`].
pub mod parsers {
    use super::*;
    use bracket::{Round, Brace};

    pub const LEXER: lexer::Parser = lexer::Parser;

    pub type Word = word::Parser;

    /// Returns a parser that replaces all Welly keywords with their [`Tree`]s.
    pub fn word() -> Word {
        let mut ret = Word::default();
        ret.add_keywords::<expr::Operator>();
        ret.add_keywords::<expr::Keyword>();
        ret.add_keywords::<stmt::Keyword>();
        ret.add_keywords::<stmt::AssignOp>();
        ret
    }

    pub type Brackets<I, F> = bracket::Brackets<I, F>;

    /// Returns a [`Brackets`] that recognises [`Round`]s and parses their
    /// contents into [`Expr`]s.
    ///
    /// It parses a [`Stream`] containing [`Brace`]s, words, lexemes and
    /// [`char`]s.
    ///
    /// [`Expr`]: expr::Expr
    pub fn round(input: impl Stream) -> impl Stream {
        STMT.parse_stream(EXPR.parse_stream(Brackets::new('(', ')', |contents| {
            let contents = EXPR.parse_stream(contents.into_iter()).read_all();
            Round::new(contents)
        }, input)))
    }

    /// Returns a [`Brackets`] that recognises [`Brace`]s and parses their
    /// contents into [`Stmt`]s.
    ///
    /// It parses a [`Stream`] containing words, lexemes and [`char`]s.
    ///
    /// [`Stmt`]: stmt::Stmt
    pub fn brace(input: impl Stream) -> impl Stream {
        round(Brackets::new('{', '}', |contents| {
            let contents = round(contents.into_iter()).read_all();
            Brace::new(contents)
        }, input))
    }

    pub const EXPR: expr::Parser = expr::Parser;
    pub const STMT: stmt::Parser = stmt::Parser;
}

mod valid;
pub use valid::{Invalid, AST};

pub mod ast;

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {}
