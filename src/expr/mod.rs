use super::{lexer, word, bracket, Tree, Stream, Context, Parse};
use lexer::{Comment};
use word::{Whitespace, Alphanumeric};
use bracket::{Round, Brace};

mod op;
pub use op::{Precedence, Op};

mod atom;
pub use atom::{Operator};

mod precedence;
use precedence::{Stack};

pub const MISSING_FIELD: &'static str = "Missing field name";
pub const MISSING_ARGS: &'static str = "Missing function arguments";
pub const MISSING_RETURN_TYPE: &'static str = "Missing function return type";

// ----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Keyword { Fn, Dot }

impl Tree for Keyword {
    fn declare_keywords(mut declare: impl FnMut(&'static str, Self)) {
        declare("fn", Self::Fn);
        declare(".", Self::Dot);
    }
}

// ----------------------------------------------------------------------------

/// Represents a possibly missing [`Expr`].
pub type MaybeExpr = Option<Box<Expr>>;

/// Represents an expression.
#[derive(Debug)]
pub enum Expr {
    /// A literal character value.
    Char(char),

    /// A literal string value.
    String(String),

    /// An identifier or literal number value.
    Name(String),

    /// Comma-separated [`Expr`]s in round brackets.
    Round(Round),

    /// A function or function type literal.
    Function(Option<String>, Round, MaybeExpr, Option<Brace>),

    /// A keyword operator applied to zero, one or two operands.
    Op(MaybeExpr, Op, MaybeExpr),

    /// Field access.
    Field(MaybeExpr, String),

    /// Function or macro call.
    Call(MaybeExpr, Round),
}

impl Tree for Expr {}

// ----------------------------------------------------------------------------

/// Read and discard [`Whitespace`]s and [`Comment]`s, if possible.
fn skip(input: &mut Context<impl Stream>) -> Result<(), String> {
    while input.read::<Whitespace>()?.is_some() || input.read::<Comment>()?.is_some() {
        input.pop();
    }
    Ok(())
}

#[derive(Default, Debug)]
pub struct Parser;

impl Parser {
    /// Parse a field access, starting after the `.`.
    fn parse_field(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<Alphanumeric>, String> {
        input.read::<Alphanumeric>()?.ok_or_else(|| MISSING_FIELD.into())
    }

    /// Parse a function or function type literal, starting after the `fn`.
    fn parse_function(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Expr, String> {
        skip(input)?;
        let name = input.read::<Alphanumeric>()?.map(|name| name.0);
        let args = *input.read::<Round>()?.ok_or_else(|| MISSING_ARGS)?;
        skip(input)?;
        let return_type = if let Some(c) = input.read::<char>()? {
            if *c == ':' {
                skip(input)?;
                if let Some(type_name) = input.read::<Alphanumeric>()? {
                    Some(Box::new(Expr::Name(type_name.0)))
                } else if let Some(round) = input.read::<Round>()? {
                    Some(Box::new(Expr::Round(*round)))
                } else {
                    Err(MISSING_RETURN_TYPE)?
                }
            } else {
                input.unread(c);
                None
            }
        } else {
            None
        };
        skip(input)?;
        let body = input.read::<Brace>()?.map(|body| *body);
        Ok(Expr::Function(name, args, return_type, body))
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        let mut stack = Stack::default();
        loop {
            skip(input)?;
            if let Some(tree) = input.read::<word::Alphanumeric>()? {
                stack.nonfix(Expr::Name(tree.0));
            } else if let Some(tree) = input.read::<bracket::Round>()? {
                if stack.has_expr() {
                    stack.postfix(Precedence::MAX, |expr| Expr::Call(expr, *tree));
                } else {
                    stack.nonfix(Expr::Round(*tree));
                }
            } else if let Some(tree) = input.read::<Operator>()? {
                stack.op(if stack.has_expr() { tree.with_left } else { tree.without_left });
            } else if let Some(keyword) = input.read::<Keyword>()? {
                match *keyword {
                    Keyword::Fn => {
                        stack.nonfix(self.parse_function(input)?);
                    },
                    Keyword::Dot => {
                        let field = self.parse_field(input)?;
                        stack.postfix(Precedence::MAX, |expr| Expr::Field(expr, field.0));
                    },
                }
            } else if let Some(tree) = input.read::<lexer::CharacterLiteral>()? {
                stack.nonfix(Expr::Char(tree.0));
            } else if let Some(tree) = input.read::<lexer::StringLiteral>()? {
                stack.nonfix(Expr::String(tree.0));
            } else {
                break;
            }
        }
        Ok(if let Some(expr) = stack.flush() { expr } else { input.read_any()? })
    }
}
