use std::{fmt};

use super::{enums, loc, parser, Validate, Name, Expr, Pattern};
use enums::{Separator, Op, ItemWord};
use loc::{Location, Loc, Locate};
use parser::{Doc, Item};

pub const BAD_NAME: &'static str = "Expected a name";
pub const BAD_CALL: &'static str = "Expected ( ... )";
pub const MISSING_LHS: &'static str = "Expected a pattern before this assignment operator";
pub const MISSING_RHS: &'static str = "Expected an expression after this assignment operator";
pub const MISSING_NAME: &'static str = "Expected a name after this keyword";
pub const MISSING_EXPR: &'static str = "Expected an expression after this keyword";
pub const MISSING_BLOCK: &'static str = "Expected { ... } after this statement";
pub const EXTRA_BLOCK: &'static str = "Unexpected { ... }";
pub const MISSING_STMT: &'static str = "Expected a statement";
pub const MISSING_SEMICOLON: &'static str = "This statement must be followed by a semicolon";

// ----------------------------------------------------------------------------

/// Checks that `expr` is a `Name`.
fn to_name(expr: Expr) -> loc::Result<Loc<Name>> {
    let ret = match expr {
        Expr::Name(name) => name,
        expr => Err(Loc(BAD_NAME, expr.loc()))?,
    };
    Ok(ret)
}

/// Checks whether `expr` is of the form `expr: type` or just `expr`.
/// Returns `(name, type)`.
fn remove_cast(expr: Expr) -> (Expr, Option<Expr>) {
    match expr {
        Expr::Op(Some(expr), Loc(Op::Cast, _), Some(return_type)) => (*expr, Some(*return_type)),
        expr => (expr, None),
    }
}

/// Checks whether `expr` is of the form `name(expr)` or just `expr`.
/// `name`is optional.
/// `expr` can be an [`Expr::Group`] or an [`Expr::Tuple`].
fn remove_call(expr: Expr) -> loc::Result<(Option<Loc<Name>>, Expr)> {
    let (name, expr) = match expr {
        Expr::Call(name, expr) => (Some(to_name(*name)?), *expr),
        expr => (None, expr),
    };
    if !matches!(&expr, Expr::Group(_) | Expr::Tuple(_)) { Err(Loc(BAD_CALL, expr.loc()))? }
    Ok((name, expr))
}

// ----------------------------------------------------------------------------

/// A statement: a program fragment that does not compute a value.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// All [`Expr`]s are `Stmt`s.
    Expr(Expr),

    /// `pattern op= expr` evaluates the [`Expr`], unpacks it and mutate names
    /// in the [`Pattern`].
    Assign(Box<Pattern>, Loc<Option<Op>>, Box<Expr>),

    /// `impl trait { ... }` adds a trait implementation to an object.
    ///
    /// Illegal outside an object.
    Implementation(Location, Box<Expr>, Loc<Block>),

    /// `return expr` returns from a function.
    /// `expr` is optional.
    ///
    /// Illegal outside a function.
    Return(Location, Option<Box<Expr>>),

    /// `match expr` jumps to a `case`.
    Match(Location, Box<Expr>),

    /// `{ ... }` executes the statements in the `Block`.
    Block(Loc<Block>),
}

impl Stmt {
    /// Construct a `Self::Assign`.
    pub fn assign(lhs: Pattern, op: Loc<Option<Op>>, rhs: Expr) -> Self {
        Self::Assign(Box::new(lhs), op, Box::new(rhs))
    }

    /// Construct a `Self::Implementation`.
    pub fn implementation(word: Location, trait_: Expr, block: Loc<Block>) -> Self {
        Self::Implementation(word, Box::new(trait_), block)
    }

    /// Construct a `Self::Return`.
    pub fn return_(word: Location, expr: impl Into<Option<Expr>>) -> Self {
        Self::Return(word, expr.into().map(Box::new))
    }

    /// Construct a `Self::Match`.
    pub fn match_(word: Location, expr: Expr) -> Self { Self::Match(word, Box::new(expr)) }
}

impl Locate for Stmt {
    fn loc_start(&self) -> usize {
        match self {
            Self::Expr(expr) => expr.loc_start(),
            Self::Assign(lhs, _, _) => lhs.loc_start(),
            Self::Implementation(word, _, _) => word.loc_start(),
            Self::Return(word, _) => word.loc_start(),
            Self::Match(word, _) => word.loc_start(),
            Self::Block(block) => block.loc_start(),
        }
    }

    fn loc_end(&self) -> usize {
        match self {
            Self::Expr(expr) => expr.loc_end(),
            Self::Assign(_, _, rhs) => rhs.loc_end(),
            Self::Implementation(_, _, block) => block.loc_end(),
            Self::Return(_, Some(expr)) => expr.loc_end(),
            Self::Return(word, None) => word.loc_end(),
            Self::Match(_, expr) => expr.loc_end(),
            Self::Block(block) => block.loc_end(),
        }
    }
}

impl Validate<Item> for Stmt {
    fn validate(tree: &Item) -> loc::Result<Self> {
        let ret = match tree {
            Item::Eval(formula) => Self::Expr(Expr::validate(formula)?),
            Item::Assign(lhs, op, rhs) => {
                let Some(lhs) = lhs else { Err(Loc(MISSING_LHS, op.1))? };
                let Some(rhs) = rhs else { Err(Loc(MISSING_RHS, op.1))? };
                let lhs = Pattern::validate(lhs)?;
                let rhs = Expr::validate(rhs)?;
                Self::assign(lhs, *op, rhs)
            },
            Item::Verb(word, formula, bracket) => {
                let expr = Option::<Expr>::validate(formula)?;
                let block = Option::<Loc<Block>>::validate(bracket)?;
                match word.0 {
                    ItemWord::Module => {
                        let name = if let Some(expr) = expr { Some(to_name(expr)?) } else { None };
                        if name.is_none() && block.is_none() { Err(Loc(MISSING_NAME, word.1))? }
                        Self::Expr(Expr::Module(word.1, block).named(name))
                    },
                    ItemWord::Object => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        let (name, expr) = remove_call(expr)?;
                        let parameter = Pattern::from_expr(expr)?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Self::Expr(Expr::object(word.1, parameter, block).named(name))
                    },
                    ItemWord::Function | ItemWord::Macro => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        let (expr, return_type) = remove_cast(expr);
                        let (name, expr) = remove_call(expr)?;
                        let parameter = Pattern::from_expr(expr)?;
                        Self::Expr(Expr::function(*word, parameter, return_type, block).named(name))
                    },
                    ItemWord::Trait => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let name = to_name(expr)?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Self::Expr(Expr::Trait(word.1, block).named(name))
                    },
                    ItemWord::Implementation => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Self::implementation(word.1, expr, block)
                    },
                    ItemWord::Return => {
                        if let Some(block) = block { Err(Loc(EXTRA_BLOCK, block.1))? }
                        Self::return_(word.1, expr)
                    },
                    ItemWord::Match => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        if let Some(block) = block { Err(Loc(EXTRA_BLOCK, block.1))? }
                        Self::match_(word.1, expr)
                    },
                    ItemWord::Case => todo!(),
                    ItemWord::If => todo!(),
                    ItemWord::While => todo!(),
                    ItemWord::For => todo!(),
                    ItemWord::Else => todo!(),
                }
            },
            Item::Block(bracket) => Stmt::Block(Loc::<Block>::validate(bracket)?),
            _ => { Err(Loc(MISSING_STMT, tree.loc()))? },
        };
        Ok(ret)
    }
}

impl Validate<Doc<Item>> for Stmt {
    fn validate(tree: &Doc<Item>) -> loc::Result<Self> { Ok(Self::validate(&tree.0)?) }
}


// ----------------------------------------------------------------------------

/// Zero or more `Stmt`s enclosed in `{ ... }`.
#[derive(Clone)]
pub struct Block(Box<[Stmt]>);

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl Validate<[Doc<Item>]> for Block {
    fn validate(tree: &[Doc<Item>]) -> loc::Result<Self> {
        let mut contents = Vec::new();
        let mut iter = tree.iter();
        while let Some(item) = iter.next() {
            let stmt = Stmt::validate(item)?;
            if item.0.requires_semicolon() {
                match iter.next() {
                    Some(Doc(Item::Separator(Loc(Separator::Semicolon, _)), _)) => {},
                    _ => { Err(Loc(MISSING_SEMICOLON, stmt.loc()))? },
                }
            }
            // TODO: `else`.
            contents.push(stmt);
        }
        Ok(Block(contents.into()))
    }
}
