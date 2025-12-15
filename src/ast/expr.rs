use std::{fmt};
use std::rc::{Rc};

use super::{enums, loc, parser, lexer, Validate, Name, Tag, Pattern, stmt, Stmt, Block};
use enums::{Separator, Op, ItemWord};
use loc::{Location, Loc, Locate};
use parser::{Doc, Formula, Item};
use lexer::{Atom};

pub const BAD_SELECTOR: &'static str = "Expected a field selector";
pub const STMT_NOT_EXPR: &'static str = "This statement does not have a value";
pub const BAD_ALPHANUMERIC: &'static str = "This is not an identifier, a tag or an integer";
pub const MISSING_COMMA: &'static str = "Expected a comma after this expression";

// ----------------------------------------------------------------------------

/// Identifies a field or a tuple of fields, or removes a [`Tag`].
#[derive(Clone)]
pub enum Selector {
    /// By name.
    Name(Name),

    /// By position.
    Index(i64),
}

impl Selector {
    /// Checks that `expr` is a valid [`Selector`].
    fn from_expr(expr: Expr) -> loc::Result<Loc<Self>> {
        let ret = match expr {
            Expr::Name(name) => name.map(Self::Name),
            Expr::Int(index) => index.map(Self::Index),
            e => { Err(Loc(BAD_SELECTOR, e.loc()))? },
        };
        Ok(ret)
    }
}

impl fmt::Debug for Selector {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Name(name) => name.fmt(f),
            Self::Index(index) => index.fmt(f),
        }
    }
}

// ----------------------------------------------------------------------------

/// Distinguishes functions from macros.
#[derive(Debug, Copy, Clone)]
pub struct IsMacro(pub bool);

impl From<ItemWord> for IsMacro {
    fn from(value: ItemWord) -> Self {
        IsMacro(match value {
            ItemWord::Function => false,
            ItemWord::Macro => true,
            _ => panic!("Wrong word"),
        })
    }
}

// ----------------------------------------------------------------------------

#[derive(Clone)]
pub enum Expr {
    /// An `Expr` that binds a `Name`.
    Named(Loc<Name>, Box<Expr>),

    /// `mod name { ... }` defines a module.
    ///
    /// The items in the module are declared inline in the `Block`, if any,
    /// otherwise they are read from another source file.
    Module(Location, Option<Loc<Block>>),

    /// `obj name( ... ) { ... }` defines an object type.
    ///
    /// [`Name`]s in the patterns become the object's fields.
    Object(Location, Box<Pattern>, Loc<Block>),

    /// `fn name(parameter): return_type { body }` defines a function.
    /// `macro ...` defines a macro.
    ///
    /// `name`, `return_type` and `body` are optional.
    /// [`Name`]s in the patterns become the function's arguments.
    Function(Loc<IsMacro>, Box<Pattern>, Option<Box<Expr>>, Option<Loc<Block>>),

    /// `trait name { ... }` defines a trait.
    Trait(Location, Loc<Block>),

    /// A literal `char`.
    Char(Loc<char>),

    /// A literal `str`.
    Str(Loc<Rc<str>>),

    /// A literal `i64`.
    Int(Loc<i64>),

    /// A literal [`Tag`].
    Tag(Loc<Tag>),

    /// Read the value of a `Name`.
    Name(Loc<Name>),

    /// An `Expr` in brackets.
    Group(Loc<Box<Expr>>),

    /// `( ... )` constructs a tuple.
    Tuple(Loc<Box<[Expr]>>),

    /// `[ ... ]` constructs a tuple type.
    TupleType(Loc<Box<[Expr]>>),

    /// `struct name( ... )` constructs a tuple type with names.
    Structure(Location, Box<Pattern>),

    /// `expr.TAG` removes `TAG` from `expr` otherwise does `match expr`.
    When(Box<Expr>, Loc<Tag>),

    /// `expr.name` reads field `name` of `expr`.
    Dot(Box<Expr>, Loc<Selector>),

    /// `expr op expr` applies `op` to up to two operands.
    Op(Option<Box<Expr>>, Loc<Op>, Option<Box<Expr>>),

    /// `expr( ... )` calls `expr` passing arguments.
    Call(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Optionally wrap `self` in `Self::Named`.
    pub fn named(self, name: impl Into<Option<Loc<Name>>>) -> Self {
        if let Some(name) = name.into() { Self::Named(name, Box::new(self)) } else { self }
    }

    /// Construct a `Self::Object`.
    pub fn object(word: Location, args: Pattern, body: Loc<Block>) -> Self {
        Self::Object(word, Box::new(args), body)
    }

    /// Construct a `Self::Function`.
    pub fn function(
        word: Loc<impl Into<IsMacro>>,
        parameter: Pattern,
        return_type: impl Into<Option<Self>>,
        body: impl Into<Option<Loc<Block>>>,
    ) -> Self {
        Self::Function(Loc(word.0.into(), word.1), Box::new(parameter), return_type.into().map(Box::new), body.into())
    }

    /// Construct a `Self::Group`.
    pub fn group(expr: Loc<Self>) -> Self { Self::Group(Loc(Box::new(expr.0), expr.1)) }

    /// Construct a `Self::Tuple`.
    pub fn tuple(args: Loc<impl Into<Box<[Expr]>>>) -> Self { Self::Tuple(Loc(args.0.into(), args.1)) }

    /// Construct a `Self::TupleType`.
    pub fn tuple_type(args: Loc<impl Into<Box<[Expr]>>>) -> Self { Self::TupleType(Loc(args.0.into(), args.1)) }

    /// Construct a `Self::Structure`.
    pub fn structure(word: Location, pattern: Pattern) -> Self { Self::Structure(word, Box::new(pattern)) }

    /// Construct a `Self::When`.
    pub fn when(self, tag: Loc<Tag>) -> Self { Self::When(Box::new(self), tag) }

    /// Construct a `Self::Dot`.
    pub fn dot(self, selector: Loc<Selector>) -> Self { Self::Dot(Box::new(self), selector) }

    /// Construct a `Self::Op`.
    pub fn op(left: impl Into<Option<Self>>, op: Loc<Op>, right: impl Into<Option<Self>>) -> Self {
        Self::Op(left.into().map(Box::new), op, right.into().map(Box::new))
    }

    /// Construct a `Self::Call`.
    pub fn call(self, arg: Self) -> Self { Self::Call(Box::new(self), Box::new(arg)) }
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Named(name, expr) => f.debug_tuple("Named").field(name).field(expr).finish(),
            Self::Module(word, block) => {
                let mut t = f.debug_tuple("Module");
                t.field(word);
                if let Some(block) = block { t.field(block); }
                t.finish()
            },
            Self::Object(word, pattern, block) => {
                f.debug_tuple("Object").field(word).field(pattern).field(block).finish()
            },
            Self::Function(is_macro, pattern, return_type, block) => {
                let mut t = f.debug_tuple(if is_macro.0.0 { "Macro" } else { "Function" });
                t.field(pattern).field(return_type).field(block).finish()
            },
            Self::Trait(word, block) => f.debug_tuple("Trait").field(word).field(block).finish(),
            Self::Char(c) => c.fmt(f),
            Self::Str(s) => s.fmt(f),
            Self::Int(i) => i.fmt(f),
            Self::Tag(tag) => tag.fmt(f),
            Self::Name(name) => name.fmt(f),
            Self::Group(expr) => f.debug_tuple("Group").field(&expr.0).finish(),
            Self::Tuple(exprs) => {
                let mut t = f.debug_tuple("Tuple");
                for expr in &exprs.0 { t.field(expr); }
                t.finish()
            },
            Self::TupleType(types) => {
                let mut t = f.debug_tuple("TupleType");
                for type_ in &types.0 { t.field(type_); }
                t.finish()
            },
            Self::Structure(word, pattern) => f.debug_tuple("Structure").field(word).field(pattern).finish(),
            Self::When(expr, tag) => f.debug_tuple("When").field(expr).field(tag).finish(),
            Self::Dot(expr, selector) => f.debug_tuple("Dot").field(expr).field(selector).finish(),
            Self::Op(left, op, right) => {
                let mut t = f.debug_tuple("Op");
                if let Some(left) = left { t.field(left); }
                t.field(op);
                if let Some(right) = right { t.field(right); }
                t.finish()
            },
            Self::Call(function, argument) => f.debug_tuple("Call").field(function).field(argument).finish(),
        }
    }
}

impl Locate for Expr {
    fn loc_start(&self) -> usize {
        match self {
            Self::Named(_, expr) => expr.loc_start(),
            Self::Module(word, _) => word.loc_start(),
            Self::Object(word, _, _) => word.loc_start(),
            Self::Function(is_macro, _, _, _) => is_macro.loc_start(),
            Self::Trait(word, _) => word.loc_start(),
            Self::Char(c) => c.loc_start(),
            Self::Str(s) => s.loc_start(),
            Self::Int(i) => i.loc_start(),
            Self::Tag(tag) => tag.loc_start(),
            Self::Name(name) => name.loc_start(),
            Self::Group(expr) => expr.loc_start(),
            Self::Tuple(exprs) => exprs.loc_start(),
            Self::TupleType(types) => types.loc_start(),
            Self::Structure(word, _) => word.loc_start(),
            Self::When(expr, _) => expr.loc_start(),
            Self::Dot(expr, _) => expr.loc_start(),
            Self::Op(Some(expr), _, _) => expr.loc_start(),
            Self::Op(None, op, _) => op.loc_start(),
            Self::Call(expr, _) => expr.loc_start(),
        }
    }

    fn loc_end(&self) -> usize {
        match self {
            Self::Named(name, expr) => match &**expr {
                Self::Module(_, None) => name.loc_end(),
                _ => expr.loc_end(),
            },
            Self::Module(_, Some(block)) => block.loc_end(),
            Self::Module(word, None) => word.loc_end(), // Shouldn't happen.
            Self::Object(_, _, block) => block.loc_end(),
            Self::Function(_, _, _, Some(body)) => body.loc_end(),
            Self::Function(_, _, Some(return_type), None) => return_type.loc_end(),
            Self::Function(_, parameter, None, None) => parameter.loc_end(),
            Self::Trait(_, block) => block.loc_end(),
            Self::Char(c) => c.loc_end(),
            Self::Str(s) => s.loc_end(),
            Self::Int(i) => i.loc_end(),
            Self::Tag(tag) => tag.loc_end(),
            Self::Name(name) => name.loc_end(),
            Self::Group(expr) => expr.loc_end(),
            Self::Tuple(exprs) => exprs.loc_end(),
            Self::TupleType(types) => types.loc_end(),
            Self::Structure(_, pattern) => pattern.loc_end(),
            Self::When(_, tag) => tag.loc_end(),
            Self::Dot(_, selector) => selector.loc_end(),
            Self::Op(_, _, Some(expr)) => expr.loc_end(),
            Self::Op(_, op, None) => op.loc_end(),
            Self::Call(_, args) => args.loc_end(),
        }
    }
}

impl Validate<Loc<Atom>> for Expr {
    fn validate(tree: &Loc<Atom>) -> loc::Result<Self> {
        let ret = match &tree.0 {
            Atom::CharLiteral(c) => Self::Char(Loc(*c, tree.1)),
            Atom::StrLiteral(s) => Self::Str(Loc(s.clone(), tree.1)),
            Atom::Alphanumeric(s) => {
                if let Some(tag) = Tag::new(s) { Self::Tag(Loc(tag, tree.1)) }
                else if let Some(name) = Name::new(s) { Self::Name(Loc(name, tree.1)) }
                else if let Ok(int) = s.parse::<i64>() { Self::Int(Loc(int, tree.1)) }
                else if let Ok(int) = s.parse::<u64>() { Self::Int(Loc(int as i64, tree.1)) }
                else { Err(Loc(BAD_ALPHANUMERIC, tree.1))? }
            },
        };
        Ok(ret)
    }
}

impl Validate<Formula> for Expr {
    fn validate(tree: &Formula) -> loc::Result<Self> {
        let ret = match tree {
            Formula::Atom(atom) => Self::validate(atom)?,
            Formula::RoundGroup(bracket) => {
                match CommaSeparated::validate(&bracket.0)?.number() {
                    Number::One(expr) => Self::group(Loc(expr, bracket.1)),
                    Number::Many(exprs) => Self::tuple(Loc(exprs, bracket.1)),
                }
            },
            Formula::SquareGroup(bracket) => {
                match CommaSeparated::validate(&bracket.0)?.number() {
                    Number::One(expr) => Self::group(Loc(expr, bracket.1)),
                    Number::Many(exprs) => Self::tuple_type(Loc(exprs, bracket.1)),
                }
            },
            Formula::Op(left, op, right) => {
                let left = Option::<Expr>::validate(left)?;
                let right = Option::<Expr>::validate(right)?;
                match op.0 {
                    Op::Structure => {
                        assert!(left.is_none(), "Structure has no left operand");
                        let right = right.expect("Structure has a right operand");
                        let (name, right) = stmt::remove_call(right)?;
                        let name = if let Some(name) = name { Some(stmt::to_name(name)?) } else { None };
                        let pattern = Pattern::from_expr(right)?;
                        Self::structure(op.1, pattern).named(name)
                    },
                    Op::Dot => {
                        let left = left.expect("Dot has a left operand");
                        let right = right.expect("Dot has a right operand");
                        if let Expr::Tag(tag) = right {
                            left.when(tag)
                        } else {
                            left.dot(Selector::from_expr(right)?)
                        }
                    },
                    _ => {
                        Self::op(left, *op, right)
                    },
                }
            }
            Formula::RoundCall(function, bracket) => {
                let function = Expr::validate(&**function)?;
                let arg = match CommaSeparated::validate(&bracket.0)?.number() {
                    Number::One(expr) => Self::group(Loc(expr, bracket.1)),
                    Number::Many(exprs) => Self::tuple(Loc(exprs, bracket.1)),
                };
                function.call(arg)
            }
            Formula::SquareCall(function, bracket) => {
                let function = Expr::validate(&**function)?;
                let arg = match CommaSeparated::validate(&bracket.0)?.number() {
                    Number::One(expr) => Self::group(Loc(expr, bracket.1)),
                    Number::Many(exprs) => Self::tuple(Loc(exprs, bracket.1)),
                };
                function.call(arg)
            }
        };
        Ok(ret)
    }
}

impl Validate<Box<Formula>> for Expr {
    fn validate(tree: &Box<Formula>) -> loc::Result<Self> { Ok(Self::validate(&**tree)?) }
}

impl Validate<Item> for Expr {
    fn validate(tree: &Item) -> loc::Result<Self> {
        let ret = match Stmt::validate(tree)? {
            Stmt::Expr(expr) => expr,
            s => { Err(Loc(STMT_NOT_EXPR, s.loc()))? },
        };
        Ok(ret)
    }
}

impl Validate<Doc<Item>> for Expr {
    fn validate(tree: &Doc<Item>) -> loc::Result<Self> { Ok(Self::validate(&tree.0)?) }
}

// ----------------------------------------------------------------------------

/// The return type of `CommaSeparated::number()`.
pub enum Number {
    /// One [`Expr`] not followed by a comma.
    One(Expr),

    /// Zero or two or more [`Expr`]s, or one followed by a comma.
    Many(Box<[Expr]>),
}

/// Zero or more `V`s, separated by commas, and optionally followed by a comma.
struct CommaSeparated(Box<[Expr]>, bool);

impl CommaSeparated {
    /// Distinguish a tuple from a group.
    fn number(self) -> Number {
        if self.1 || self.0.len() != 1 { return Number::Many(self.0); }
        Number::One(self.0.into_iter().next().expect("Already checked"))
    }
}

impl Validate<[Doc<Item>]> for CommaSeparated {
    fn validate(tree: &[Doc<Item>]) -> loc::Result<Self> {
        let mut contents = Vec::new();
        let mut has_comma = true;
        let mut iter = tree.iter();
        while let Some(item) = iter.next() {
            contents.push(Expr::validate(item)?);
            match iter.next() {
                None => { has_comma = false; break; },
                Some(Doc(Item::Separator(Loc(Separator::Comma, _)), _)) => {},
                _ => {
                    let loc = contents.last().expect("Just pushed").loc();
                    Err(Loc(MISSING_COMMA, loc))?
                },
            }
        }
        Ok(Self(contents.into(), has_comma))
    }
}
