use std::{fmt};

use super::{enums, loc, parser, Validate, Expr, Pattern};
use enums::{Op, Separator};
use loc::{Location, Loc, Locate};
use parser::{Doc, Item};

pub const MISSING_LHS: &'static str = "Expected a pattern before this assignment operator";
pub const MISSING_RHS: &'static str = "Expected an expression after this assignment operator";
pub const MISSING_STMT: &'static str = "Expected a statement";
pub const MISSING_SEMICOLON: &'static str = "This statement must be followed by a semicolon";

// ----------------------------------------------------------------------------

/// A statement: a program fragment that does not compute a value.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// All [`Expr`]s are `Stmt`s.
    Expr(Expr),

    /// `pattern op= expr` evaluates the [`Expr`], unpacks it and mutate names
    /// in the [`Pattern`].
    Assign(Pattern, Loc<Option<Op>>, Expr),

    /// `impl trait { ... }` adds a trait implementation to an object.
    ///
    /// Illegal outside an object.
    Implementation(Location, Expr, Loc<Block>),

    /// `{ ... }` executes the statements in the `Block`.
    Block(Loc<Block>),
}

impl Stmt {
    fn requires_semicolon(&self) -> bool {
        match self {
            Self::Expr(_) => true,
            Self::Assign(_, _, _) => true,
            Self::Implementation(_, _, _) => false,
            Self::Block(_) => false,
        }
    }
}

impl Locate for Stmt {
    fn loc_start(&self) -> usize {
        match self {
            Self::Expr(expr) => expr.loc_start(),
            Self::Assign(lhs, _, _) => lhs.loc_start(),
            Self::Implementation(word, _, _) => word.loc_start(),
            Self::Block(block) => block.loc_start(),
        }
    }

    fn loc_end(&self) -> usize {
        match self {
            Self::Expr(expr) => expr.loc_end(),
            Self::Assign(_, _, rhs) => rhs.loc_end(),
            Self::Implementation(_, _, block) => block.loc_end(),
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
                Self::Assign(lhs, *op, rhs)
            },
            Item::Verb(_, _) => todo!(),
            Item::Control(_, _, _) => todo!(),
            Item::Block(bracket) => Stmt::Block(Loc::validate(bracket)?),
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
            if stmt.requires_semicolon() {
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
