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

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::{bracket, EndOfFile, Characters};
    use bracket::{Round, Brace};
    use super::*;

    /// Parse a [`Stream`] containing [`Round`]s and [`Brace`]s into [`Expr`]s.
    fn expr(input: impl Stream) -> impl Stream {
        crate::Parser::new(super::Parser, input)
    }

    /// Parse a [`Stream`] containing [`Brace`]s into [`Round`]s and [`Expr`]s.
    fn round(input: impl Stream) -> impl Stream {
        expr(bracket::Parser::new('(', ')', |contents| {
            let contents = expr(contents.into_iter()).read_all();
            Box::new(Round(contents))
        }, input))
    }

    /// Parse a [`Stream`] into [`Brace`]s, [`Round`]s and [`Expr`]s.
    fn brace(input: impl Stream) -> impl Stream {
        round(bracket::Parser::new('{', '}', |contents| {
            let contents = round(contents.into_iter()).read_all();
            Box::new(Brace(contents))
        }, input))
    }

    /// Parse `source` into a single [`Expr`].
    fn parse(source: &str) -> Box<Expr> {
        let stream = Characters::new(source);
        let stream = crate::Parser::new(lexer::Parser, stream);
        let mut word_parser = word::Parser::default();
        word_parser.add_keywords::<Operator>();
        word_parser.add_keywords::<Keyword>();
        let stream = crate::Parser::new(word_parser, stream);
        let mut stream = brace(stream);
        let result = match stream.read().1 {
            Ok(tree) => match tree.downcast::<Expr>() {
                Ok(tree) => tree,
                Err(tree) => panic!("Got a non-Expr: {:?}", tree),
            },
            Err(e) => panic!("Got error: {:?}", e),
        };
        assert!(stream.read().is::<EndOfFile>());
        result
    }

    /// Check that `e` is of the form `Some(Expr::Op(left, expected, right))`
    /// and return `(left, right)`.
    fn check_op(e: impl Into<MaybeExpr>, expected: Op) -> (MaybeExpr, MaybeExpr) {
        match *e.into().expect("Missing Expr::Op") {
            Expr::Op(left, observed, right) => {
                assert_eq!(expected, observed);
                (left, right)
            },
            e => panic!("Expected an Expr::Op but got {:?}", e),
        }
    }

    /// Check that `e` is of the form `Some(Expr::Name(expected))`.
    fn check_name(e: impl Into<MaybeExpr>, expected: &'static str) {
        match *e.into().expect("Missing Expr::Name") {
            Expr::Name(observed) => assert_eq!(expected, observed),
            e => panic!("Expected an Expr::Name but got {:?}", e),
        }
    }

    /// Check that `e` is of the form `Some(Expr::Field(object, expected))`
    /// and return `object`.
    fn check_field(e: impl Into<MaybeExpr>, expected: &'static str) -> MaybeExpr {
        match *e.into().expect("Missing Expr::Field") {
            Expr::Field(object, observed) => {
                assert_eq!(expected, observed);
                object
            },
            e => panic!("Expected an Expr::Name but got {:?}", e),
        }
    }

    #[test]
    fn missing() {
        let tree = parse("a b");
        println!("tree = {:#?}", tree);
        let (a, b) = check_op(tree, Op::Missing);
        check_name(a, "a");
        check_name(b, "b");
    }

    #[test]
    fn ergonomics1() {
        let tree = parse("item in low .. high and condition");
        println!("tree = {:#?}", tree);
        let (tree, condition) = check_op(tree, Op::BoolAnd);
        check_name(condition, "condition");
        let (item, tree) = check_op(tree, Op::In);
        check_name(item, "item");
        let (low, high) = check_op(tree, Op::Exclusive);
        check_name(low, "low");
        check_name(high, "high");
    }

    #[test]
    fn ergonomics2() {
        let tree = parse("0 == x & 1 << 4");
        println!("tree = {:#?}", tree);
        let (zero, tree) = check_op(tree, Op::EQ);
        check_name(zero, "0");
        let (x, tree) = check_op(tree, Op::BitAnd);
        check_name(x, "x");
        let (one, four) = check_op(tree, Op::SL);
        check_name(one, "1");
        check_name(four, "4");
    }

    #[test]
    fn ergonomics3() {
        let tree = parse("-x ** 2");
        println!("tree = {:#?}", tree);
        let (none, tree) = check_op(tree, Op::Minus);
        assert!(none.is_none());
        let (x, two) = check_op(tree, Op::Pow);
        check_name(x, "x");
        check_name(two, "2");
    }

    #[test]
    fn ergonomics4() {
        let tree = parse("x == 1 + y.z");
        println!("tree = {:#?}", tree);
        let (x, tree) = check_op(tree, Op::EQ);
        check_name(x, "x");
        let (one, tree) = check_op(tree, Op::Add);
        check_name(one, "1");
        let y = check_field(tree, "z");
        check_name(y, "y");
    }

    #[test]
    fn ergonomics5() {
        let tree = parse("1 + 2 * 3");
        println!("tree = {:#?}", tree);
        let (one, tree) = check_op(tree, Op::Add);
        check_name(one, "1");
        let (two, three) = check_op(tree, Op::Mul);
        check_name(two, "2");
        check_name(three, "3");
    }

    #[test]
    fn ergonomics6() {
        let tree = parse("x + 1 << 4 * y");
        println!("tree = {:#?}", tree);
        let (left, right) = check_op(tree, Op::SL);
        let (x, one) = check_op(left, Op::Add);
        check_name(x, "x");
        check_name(one, "1");
        let (four, y) = check_op(right, Op::Mul);
        check_name(four, "4");
        check_name(y, "y");
    }

    #[test]
    fn ergonomics7() {
        let tree = parse("low ... high : type");
        println!("tree = {:#?}", tree);
        let (low, tree) = check_op(tree, Op::Inclusive);
        check_name(low, "low");
        let (high, type_) = check_op(tree, Op::Cast);
        check_name(high, "high");
        check_name(type_, "type");
    }

    #[test]
    fn ergonomics8() {
        let tree = parse("x: type >= 0");
        println!("tree = {:#?}", tree);
        let (tree, zero) = check_op(tree, Op::GE);
        check_name(zero, "0");
        let (x, type_) = check_op(tree, Op::Cast);
        check_name(x, "x");
        check_name(type_, "type");
    }
}
