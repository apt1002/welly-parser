use std::{fmt};

use super::{enums, loc, parser, Validate, Tag, Expr, Pattern};
use enums::{Separator, Op, ItemWord};
use loc::{Location, Loc, Locate};
use parser::{Doc, Item};

pub const MISSING_LHS: &'static str = "Expected a pattern before this assignment operator";
pub const MISSING_RHS: &'static str = "Expected an expression after this assignment operator";
pub const MISSING_NAME: &'static str = "Expected `name` after this keyword";
pub const MISSING_CALL: &'static str = "Expected `expression( ... )`";
pub const MISSING_EXPR: &'static str = "Expected an expression after this keyword";
pub const MISSING_BLOCK: &'static str = "Expected `{ ... }` after this statement";
pub const EXTRA_BLOCK: &'static str = "Unexpected `{ ... }`";
pub const MISSING_STMT: &'static str = "Expected a statement";
pub const EXTRA_EXPR: &'static str = "Unexpected expression";
pub const EXTRA_ELSE: &'static str = "`else` must follow an `if`, `while` or `for` statement";
pub const MISSING_SEMICOLON: &'static str = "This statement must be followed by `;`";

// ----------------------------------------------------------------------------

/// Distinguishes a  [`Stmt::Control`].
#[derive(Debug, Clone)]
pub enum Control {
    /// `if condition { ... } else { ... }` executes the body or the [`Else`].
    If(Box<Expr>),

    /// `while condition { ... } else { ... }` executes the body repeatedly
    /// then the [`Else`] (unless the body jumps somewhere else).
    While(Box<Expr>),

    /// `for pattern in sequence { ... } else { ... }` executes the body
    /// repeatedly then the [`Else`] (unless the body jumps somewhere else).
    For(Box<Pattern>, Box<Expr>),
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

    /// `case TAG( ... ) { ... }` is a target for `match`.
    Case(Location, Loc<Tag>, Box<Pattern>, Loc<Block>),

    /// Execute `body` and/or `else` depending on `control`.
    /// The `else` [`Block`] is optional.
    Control(Location, Control, Loc<Block>, Option<Loc<Block>>),

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

    /// Construct a `Self::Case`.
    pub fn case(word: Location, tag: Loc<Tag>, parameter: Pattern, block: Loc<Block>) -> Self {
        Self::Case(word, tag, Box::new(parameter), block)
    }

    /// Constructs a `Self::Control` containing a `Control::If`.
    pub fn if_(word: Location, condition: Expr, body: Loc<Block>) -> Self {
        Self::Control(word, Control::If(Box::new(condition)), body, None)
    }

    /// Constructs a `Self::Control` containing a `Control::While`.
    pub fn while_(word: Location, condition: Expr, body: Loc<Block>) -> Self {
        Self::Control(word, Control::While(Box::new(condition)), body, None)
    }

    /// Constructs a `Self::Control` containing a `Control::For`.
    pub fn for_(word: Location, pattern: Pattern, sequence: Expr, body: Loc<Block>) -> Self {
        Self::Control(word, Control::For(Box::new(pattern), Box::new(sequence)), body, None)
    }
}

impl Locate for Stmt {
    fn loc_start(&self) -> usize {
        match self {
            Self::Expr(expr) => expr.loc_start(),
            Self::Assign(lhs, _, _) => lhs.loc_start(),
            Self::Implementation(word, _, _) => word.loc_start(),
            Self::Return(word, _) => word.loc_start(),
            Self::Match(word, _) => word.loc_start(),
            Self::Case(word, _, _, _) => word.loc_start(),
            Self::Control(word, _, _, _) => word.loc_start(),
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
            Self::Case(_, _, _, block) => block.loc_end(),
            Self::Control(_, _, _, Some(block)) => block.loc_end(),
            Self::Control(_, _, block, None) => block.loc_end(),
            Self::Block(block) => block.loc_end(),
        }
    }
}

impl Validate<Item> for Stmt {
    fn validate(tree: &Item) -> loc::Result<Self> {
        let ret = match StmtOrElse::validate(tree)? {
            StmtOrElse::Stmt(stmt) => stmt,
            StmtOrElse::Else(word, _) => Err(Loc(EXTRA_ELSE, word))?,
        };
        Ok(ret)
    }
}

// ----------------------------------------------------------------------------

/// Represents a `Stmt` or `else { ... }`.
#[derive(Debug, Clone)]
pub enum StmtOrElse { Stmt(Stmt), Else(Location, Loc<Block>) }

impl Validate<Item> for StmtOrElse {
    fn validate(tree: &Item) -> loc::Result<Self> {
        let ret = match tree {
            Item::Separator(separator) => Err(Loc(MISSING_STMT, separator.loc()))?,
            Item::Eval(formula) => Stmt::Expr(Expr::validate(formula)?),
            Item::Assign(lhs, op, rhs) => {
                let Some(lhs) = lhs else { Err(Loc(MISSING_LHS, op.1))? };
                let Some(rhs) = rhs else { Err(Loc(MISSING_RHS, op.1))? };
                let lhs = Pattern::validate(lhs)?;
                let rhs = Expr::validate(rhs)?;
                Stmt::assign(lhs, *op, rhs)
            },
            Item::Verb(word, formula, bracket) => {
                let expr = Option::<Expr>::validate(formula)?;
                let block = Option::<Loc<Block>>::validate(bracket)?;
                match word.0 {
                    ItemWord::Module => {
                        let name = Expr::to_optional_name(expr)?;
                        if name.is_none() && block.is_none() { Err(Loc(MISSING_NAME, word.1))? }
                        Stmt::Expr(Expr::Module(word.1, block).named(name))
                    },
                    ItemWord::Object => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        let (name, expr) = expr.remove_call()?;
                        let Some(name) = name else { Err(Loc(MISSING_CALL, expr.loc()))? };
                        let name = name.to_name()?;
                        let parameter = Pattern::from_expr(expr)?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::Expr(Expr::object(word.1, parameter, block).named(name))
                    },
                    ItemWord::Function | ItemWord::Macro => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        let (expr, return_type) = expr.remove_cast();
                        let (name, expr) = expr.remove_call()?;
                        let name = Expr::to_optional_name(name)?;
                        let parameter = Pattern::from_expr(expr)?;
                        Stmt::Expr(Expr::function(*word, parameter, return_type, block).named(name))
                    },
                    ItemWord::Trait => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let name = expr.to_name()?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::Expr(Expr::Trait(word.1, block).named(name))
                    },
                    ItemWord::Implementation => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::implementation(word.1, expr, block)
                    },
                    ItemWord::Return => {
                        if let Some(block) = block { Err(Loc(EXTRA_BLOCK, block.1))? }
                        Stmt::return_(word.1, expr)
                    },
                    ItemWord::Match => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        if let Some(block) = block { Err(Loc(EXTRA_BLOCK, block.1))? }
                        Stmt::match_(word.1, expr)
                    },
                    ItemWord::Case => {
                        let Some(expr) = expr else { Err(Loc(MISSING_EXPR, word.1))? };
                        let (tag, expr) = expr.remove_call()?;
                        let Some(tag) = tag else { Err(Loc(MISSING_CALL, expr.loc()))? };
                        let tag = tag.to_tag()?;
                        let parameter = Pattern::from_expr(expr)?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::case(word.1, tag, parameter, block)
                    },
                    ItemWord::If => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::if_(word.1, expr, block)
                    },
                    ItemWord::While => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::while_(word.1, expr, block)
                    },
                    ItemWord::For => {
                        let Some(expr) = expr else { Err(Loc(MISSING_NAME, word.1))? };
                        let (pattern, sequence) = expr.remove_in()?;
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        Stmt::for_(word.1, pattern, sequence, block)
                    },
                    ItemWord::Else => {
                        if let Some(expr) = expr { Err(Loc(EXTRA_EXPR, expr.loc()))? }
                        let Some(block) = block else { Err(Loc(MISSING_BLOCK, tree.loc()))? };
                        return Ok(Self::Else(word.1, block));
                    },
                }
            },
            Item::Block(bracket) => Stmt::Block(Loc::<Block>::validate(bracket)?),
        };
        Ok(Self::Stmt(ret))
    }
}

// ----------------------------------------------------------------------------

/// Zero or more `Stmt`s enclosed in `{ ... }`.
#[derive(Clone)]
pub struct Block(pub Box<[Stmt]>);

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl Validate<[Doc<Item>]> for Block {
    fn validate(tree: &[Doc<Item>]) -> loc::Result<Self> {
        let mut contents = Vec::new();
        let mut iter = tree.iter();
        while let Some(Doc(item, _)) = iter.next() {
            match StmtOrElse::validate(item)? {
                StmtOrElse::Stmt(stmt) => {
                    if item.requires_semicolon() {
                        match iter.next() {
                            Some(Doc(Item::Separator(Loc(Separator::Semicolon, _)), _)) => {},
                            _ => { Err(Loc(MISSING_SEMICOLON, stmt.loc()))? },
                        }
                    }
                    contents.push(stmt);
                },
                StmtOrElse::Else(word, block) => {
                    match contents.last_mut() {
                        Some(Stmt::Control(_, _, _, Some(_))) => Err(Loc(EXTRA_ELSE, word))?,
                        Some(Stmt::Control(_, _, _, e)) => { *e = Some(block); },
                        _ => Err(Loc(EXTRA_ELSE, word))?,
                    }
                }
            }
        }
        Ok(Block(contents.into()))
    }
}
