use super::{bracket, expr, Tree, Stream, Context, Parse};
use bracket::{Brace};
use expr::{MaybeExpr, Expr, Op};

pub const MISSING_SEMICOLON: &'static str = "Missing `;`";
pub const MISSING_ELSE_BODY: &'static str = "Missing `else` body";
pub const MISSING_IF_BODY: &'static str = "Missing `if` body";
pub const MISSING_LOOP_BODY: &'static str = "Missing loop body";
pub const MISSING_CASE_BODY: &'static str = "Missing `case` body";
pub const SPURIOUS_CASE: &'static str = "Unexpected `case` without a preceding `switch`";
pub const SPURIOUS_ELSE: &'static str = "Unexpected `else` without a preceding `switch`, `if`, `while` or `for`";

// ----------------------------------------------------------------------------

/// Represents a verb keyword.
///
/// A `Verb` optionally followed by an [`Expr`] parses as a [`Stmt`].
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Verb { Break, Continue, Return, Throw, Assert, Assume }

/// Represents a statement keyword.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Keyword { Case, Else, Switch, If, While, For, Verb(Verb) }

impl Tree for Keyword {
    fn declare_keywords(mut declare: impl FnMut(&'static str, Self)) {
        declare("case", Self::Case);
        declare("else", Self::Else);
        declare("switch", Self::Switch);
        declare("if", Self::If);
        declare("while", Self::While);
        declare("for", Self::For);
        declare("break", Self::Verb(Verb::Break));
        declare("continue", Self::Verb(Verb::Continue));
        declare("return", Self::Verb(Verb::Return));
        declare("throw", Self::Verb(Verb::Throw));
        declare("assert", Self::Verb(Verb::Assert));
        declare("assume", Self::Verb(Verb::Assume));
    }
}

/// An assignment operator, e.g. the `+=` in `x += 1;`.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum AssignOp { Let, Set, Op(Op) }

impl Tree for AssignOp {
    fn declare_keywords(mut declare: impl FnMut(&'static str, Self)) {
        declare("=", Self::Let);
        declare(":=", Self::Set);
        declare("|=", Self::Op(Op::BitOr));
        declare("^=", Self::Op(Op::BitXor));
        declare("&=", Self::Op(Op::BitAnd));
        declare("<<=", Self::Op(Op::SL));
        declare(">>=", Self::Op(Op::ASR));
        declare(">>>=", Self::Op(Op::LSR));
        declare("+=", Self::Op(Op::Add));
        declare("-=", Self::Op(Op::Sub));
        declare("*=", Self::Op(Op::Mul));
        declare("/=", Self::Op(Op::Div));
        declare("%=", Self::Op(Op::Rem));
        declare("**=", Self::Op(Op::Pow));
    }
}

// ----------------------------------------------------------------------------

/// Represents an `case` clause.
///
/// Allow the pattern [`Expr`]s to be `None`, though it's an error.
#[derive(Debug)]
pub struct Case(pub MaybeExpr, pub Brace);

/// Represents a possibly missing `else` clause.
pub type MaybeElse = Option<Brace>;

/// Represents a statement, including the trailing `;` if any.
///
/// `Stmt`s frequently contain `Expr`s, and never two consecutively. We allow
/// every such `Expr` to be optional, so that a later pass can report a helpful
/// error when it's missing.
#[derive(Debug)]
pub enum Stmt {
    /// E.g. `print("Hello");`.
    Expr(MaybeExpr),

    /// E.g. `x += 1;`.
    Assign(MaybeExpr, AssignOp, MaybeExpr),

    /// E.g. `if ... {...} else {...}`.
    ///
    /// Allow the condition [`Expr`] to be `None`, though it's an error.
    If(MaybeExpr, Brace, MaybeElse),

    /// E.g. `while ... {...} else {...}`.
    ///
    /// Allow the condition [`Expr`] to be `None`, though it's an error.
    While(MaybeExpr, Brace, MaybeElse),

    /// E.g. `for ... in ... {...} else {...}`.
    ///
    /// Allow an arbitrary [`Expr`], or a missing one, though anything but
    /// `... in ...` is an error.
    For(MaybeExpr, Brace, MaybeElse),

    /// E.g. `switch ... case ... {...} case ... {...} else {...}`.
    ///
    /// Allow the discriminant [`Expr`] to be `None`, though it's an error.
    Switch(MaybeExpr, Vec<Case>, MaybeElse),

    /// E.g. `return ...;` or `continue;`.
    ///
    /// Allow the [`Expr`] to be present or missing, though for some [`Verb`]s
    /// one of those cases is an error.
    Verb(Verb, MaybeExpr),
}

impl Tree for Stmt {}

// ----------------------------------------------------------------------------

#[derive(Default, Debug)]
pub struct Parser;

impl Parser {
    /// Parse `;` otherwise it's an error.
    fn parse_semicolon(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<char, String> {
        Ok(*input.read_if(|&k| k == ';')?.ok_or(MISSING_SEMICOLON)?)
    }

    /// Parse `case pattern {...}` if possible.
    ///
    /// `case` without `{...}` is an error.
    fn parse_case(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Option<Case>, String> {
        Ok(if input.read_if(|k| matches!(k, Keyword::Case))?.is_some() {
            let pattern = input.read::<Expr>()?;
            let body = input.read::<Brace>()?.ok_or(MISSING_CASE_BODY);
            Some(Case(pattern, *body?))
        } else { None })
    }

    /// Parse `else {...}` if possible.
    ///
    /// `else` without `{...}` is an error.
    fn parse_else(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<MaybeElse, String> {
        Ok(if input.read_if(|k| matches!(k, Keyword::Else))?.is_some() {
            Some(*input.read::<Brace>()?.ok_or(MISSING_ELSE_BODY)?)
        } else { None })
    }

    /// Parse `expr {...}` optionally followed by `else {...}`.
    ///
    /// If the `{...}` is missing it's an error.
    ///
    /// - constructor - E.g. `Stmt::If`, `Stmt::While` or `Stmt::For`.
    /// - missing_body - E.g. `MISSING_IF_BODY` or `MISSING_LOOP_BODY`.
    fn parse_control(
        &self,
        input: &mut Context<impl Stream>,
        constructor: fn(MaybeExpr, Brace, MaybeElse) -> Stmt,
        missing_body: &'static str,
    ) -> Result<Box<dyn Tree>, String> {
        let condition = input.read::<Expr>()?;
        let body = input.read::<Brace>()?.ok_or(missing_body);
        let else_ = self.parse_else(input)?;
        Ok(Box::new(constructor(condition, *body?, else_)))
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        if let Some(expr) = input.read::<Expr>()? {
            if let Some(op) = input.read::<AssignOp>()? {
                let rhs = input.read::<Expr>()?;
                self.parse_semicolon(input)?;
                Ok(Box::new(Stmt::Assign(Some(expr), *op, rhs)))
            } else {
                self.parse_semicolon(input)?;
                Ok(Box::new(Stmt::Expr(Some(expr))))
            }
        } else if let Some(keyword) = input.read::<Keyword>()? {
            match *keyword {
                Keyword::Case => {
                    let _ = input.read::<Expr>()?;
                    let _ = input.read::<Brace>()?;
                    Err(SPURIOUS_CASE)?
                },
                Keyword::Else => {
                    let _ = input.read::<Brace>()?;
                    Err(SPURIOUS_ELSE)?
                },
                Keyword::Switch => {
                    let discriminant = input.read::<Expr>()?;
                    let mut cases = Vec::new();
                    while let Some(case) = self.parse_case(input)? { cases.push(case); }
                    let else_ = self.parse_else(input)?;
                    Ok(Box::new(Stmt::Switch(discriminant, cases, else_)))
                },
                Keyword::If => {
                    self.parse_control(input, Stmt::If, MISSING_IF_BODY)
                },
                Keyword::While => {
                    self.parse_control(input, Stmt::While, MISSING_LOOP_BODY)
                },
                Keyword::For => {
                    self.parse_control(input, Stmt::For, MISSING_LOOP_BODY)
                },
                Keyword::Verb(verb) => {
                    let expr = input.read::<Expr>()?;
                    self.parse_semicolon(input)?;
                    Ok(Box::new(Stmt::Verb(verb, expr)))
                },
            }
        } else if let Some(op) = input.read::<AssignOp>()? {
            // Parse `+= ...;` as an `Assign` with a missing LHS.
            let rhs = input.read::<Expr>()?;
            Ok(Box::new(Stmt::Assign(None, *op, rhs)))
        } else if input.read_if::<char>(|&k| k == ';')?.is_some() {
            // Parse `;` as a missing `Expr`.
            Ok(Box::new(Stmt::Expr(None)))
        } else { input.read_any() }
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::{lexer, word, bracket, expr, EndOfFile, Characters};
    use bracket::{Round, Brace};
    use super::*;

    /// Parse a [`Stream`] containing [`Brace`]s into [`Round`]s and [`Expr`]s.
    fn round(input: impl Stream) -> impl Stream {
        Parser.parse_stream(expr::Parser.parse_stream(bracket::Parser::new('(', ')', |contents| {
            let contents = expr::Parser.parse_stream(contents.into_iter()).read_all();
            Box::new(Round(contents))
        }, input)))
    }

    /// Parse a [`Stream`] into [`Brace`]s, [`Round`]s and [`Expr`]s.
    fn brace(input: impl Stream) -> impl Stream {
        round(bracket::Parser::new('{', '}', |contents| {
            let contents = round(contents.into_iter()).read_all();
            Box::new(Brace(contents))
        }, input))
    }

    /// Parse `source` into a [`Stream`] containing [`Stmt`]s.
    fn parse(source: &'static str) -> impl Stream {
        let stream = Characters::new(source);
        let stream = lexer::Parser.parse_stream(stream);
        let mut word_parser = word::Parser::default();
        word_parser.add_keywords::<Keyword>();
        word_parser.add_keywords::<AssignOp>();
        let stream = word_parser.parse_stream(stream);
        brace(stream)
    }

    /// Parse `source` into a single [`Stmt`].
    fn parse_one(source: &'static str) -> Box<Stmt> {
        let mut stream = parse(source);
        let result = match stream.read().1 {
            Ok(tree) => match tree.downcast::<Stmt>() {
                Ok(tree) => tree,
                Err(tree) => panic!("Got a non-Stmt: {:?}", tree),
            },
            Err(e) => panic!("Got error: {:?}", e),
        };
        assert_eq!(stream.read(), EndOfFile);
        result
    }

    /// Check that `e` is of the form `Some(Expr::Name(expected))`.
    fn check_name(e: impl Into<MaybeExpr>, expected: &'static str) {
        match *e.into().expect("Missing Expr::Name") {
            Expr::Name(observed) => assert_eq!(expected, observed),
            e => panic!("Expected an Expr::Name but got {:?}", e),
        }
    }

    /// Check that `b` is of the form `{ expected; }`.
    fn check_brace(b: impl Into<Option<Brace>>, expected: &'static str) {
        let mut contents = b.into().expect("Missing Brace").0.into_iter();
        match contents.read().unwrap::<Stmt>() {
            Stmt::Expr(e) => check_name(e, expected),
            s => panic!("Expected a Stmt::Expr but got {:#?}", s),
        }
        assert_eq!(contents.read(), EndOfFile);
    }

    #[test]
    fn print() {
        let tree = parse_one("print;");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::Expr(e) => check_name(e, "print"),
            s => panic!("Expected a Stmt::Expr but got {:#?}", s),
        }
    }

    #[test]
    fn assign() {
        let tree = parse_one("x += 1;");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::Assign(left, op, right) => {
                check_name(left, "x");
                assert_eq!(op, AssignOp::Op(Op::Add));
                check_name(right, "1");
            },
            s => panic!("Expected a Stmt::Assign but got {:#?}", s),
        }
    }

    #[test]
    fn if_() {
        let tree = parse_one("if b { foo; } else { bar; }");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::If(b, then, else_) => {
                check_name(b, "b");
                check_brace(then, "foo");
                check_brace(else_, "bar");
            },
            s => panic!("Expected a Stmt::If but got {:#?}", s),
        }
    }

    #[test]
    fn switch() {
        let tree = parse_one("switch d case FOO { foo; } else { bar; }");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::Switch(d, cases, else_) => {
                check_name(d, "d");
                let mut cases = cases.into_iter();
                match cases.next() {
                    Some(Case(pattern, body)) => {
                        check_name(pattern, "FOO");
                        check_brace(body, "foo");
                    },
                    _ => panic!("Missing Case"),
                }
                assert!(cases.next().is_none());
                check_brace(else_, "bar");
            },
            s => panic!("Expected a Stmt::Switch but got {:#?}", s),
        }
    }

    #[test]
    fn break_() {
        let tree = parse_one("break;");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::Verb(Verb::Break, None) => {},
            s => panic!("Expected a Stmt::Verb but got {:#?}", s),
        }
    }

    #[test]
    fn return_() {
        let tree = parse_one("return 42;");
        println!("tree = {:#?}", tree);
        match *tree {
            Stmt::Verb(Verb::Return, ans) => check_name(ans, "42"),
            s => panic!("Expected a Stmt::Verb but got {:#?}", s),
        }
    }
}
