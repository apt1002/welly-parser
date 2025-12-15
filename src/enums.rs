use std::{fmt};

/// Distinguishes the kinds of bracket.
#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
pub enum BracketKind {Round, Square, Curly}

// ----------------------------------------------------------------------------

/// A separator character.
#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
pub enum Separator {Comma, Semicolon}

// ----------------------------------------------------------------------------

/// Represents one of Welly's arithmetic operations or constants. See also
/// [`OpWord`].
///
/// Differences from other languages:
/// - Welly does not use `&`, `|`, `^` and `~` for bitwise operators.
/// - Welly uses prefix `&` for lend, prefix `$` for share.
/// - Welly uses prefix `*` for clone, similar to C's and Rust's dereference.
/// - Welly uses infix `|` for the union of types, similar to OCaml's patterns.
/// - In Rust, `and` is spelt `&&` and there is no `in`.
/// - In Rust, `when OK` is spelt `?`.
///   In Rust, `$` is spelt `Arc::new()` or `Arc::clone()`.
///   In Rust, `*` is sometimes spelt `.clone()`.
/// - In Python, `..` is spelt `:`, and is part of array subscription.
/// - Welly has unsigned operators, not unsigned types.
///   These include `\+`, `%+`, `>>+`, `<+`, `>+`, `<=+`, `>=+`.
///
/// [`OpWord`]: super::OpWord
#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
pub enum Op {
    /// The value `true`.
    True,

    /// The value `false`.
    False,

    /// The type `Self`.
    SelfType,

    /// `false or true` is `true`.
    Or,

    /// `false and true` is `false`.
    And,

    /// `not false` is `true`.
    Not,

    /// `item in collection` - Membership test.
    ///
    /// Also abused as part of `for item in collection { ... }`.
    In,

    /// `-3 == 5` is `false`.
    EQ,

    /// `-3 != 5` is `true`.
    NE,

    /// `-3 < 5` is true.
    SLT,

    /// `-3 <+ 5` is false.
    ULT,

    /// `5 > -3` is true.
    SGT,

    /// `5 > -3` is false.
    UGT,

    /// `-3 <= 5` is true.
    SLE,

    /// `-3 <=+ 5` is false.
    ULE,

    /// `5 >= -3` is true.
    SGE,

    /// `5 >=+ -3` is false.
    UGE,

    /// `-3 <> 5` is `true`.
    LG,

    /// `0..3` means `0, 1, 2`.
    Exclusive,

    /// `0...3` means `0, 1, 2, 3`.
    Inclusive,

    /// `x: t` - A value `x` cast to a type `t`.
    Cast,

    /// `-7 << 3` is `-28`.
    SL,

    /// `-7 >> 2` is `-2`.
    SSR,

    /// `-7 >>+ 2` is `0xFFFFFFFFFFFFFFFE`.
    USR,

    /// `3 + 5` is `8`.
    Add,

    /// `3 - 5` is `-2`.
    Sub,

    /// `-7 * 3` is `-21`.
    Mul,

    /// `-7 / 3` is `-3`.
    SDiv,

    /// `-7 /+ 3` is `0x555555555555553`.
    UDiv,

    /// `-7 % 3` is `2`.
    SRem,

    /// `-7 %+ 3` is `0`.
    URem,

    /// `OK[Int] | Err[String]` is a tagged union type.
    Union,

    /// `+3` is `3`.
    Plus,

    /// `-3` is `-3`.
    Minus,

    /// `&x` is loaned.
    Lend,

    /// `$x` is shared.
    Share,

    /// `*x` is a fresh copy of `x`.
    Clone,

    /// `struct Point(x: Int, y: Int)` defines a tuple type.
    Structure,

    /// `(-7) ^ 2` is `49`.
    Power,

    /// `structure.field` extracts the `field` component of `structure`.
    Dot,
}

// ----------------------------------------------------------------------------

/// The return type of [`Precedence::compare()`].
pub enum Associativity {Left, Right, Ambiguous}

/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Precedence {None, Or, And, Not, In, Eq, Cmp, Range, Cast, Shift, Sum, Product, Union, Prefix, Postfix, Dot, Power}

impl Precedence {
    /// Distinguishes `(_ self _) other _` from `_ self (_ other _)`.
    pub fn compare(self, other: Precedence) -> Associativity {
        use {Precedence::*, Associativity::*};
        if self < other { return Right }
        if self > other { return Left }
        match self {
            Or | And | Not | In | Sum | Product | Union | Dot => Left,
            Cast | Shift | Power => Right,
            Eq | Cmp | Range => Ambiguous,
            None | Prefix | Postfix => { panic!("Associativity only makes sense for infix operators"); },
        }
    }
}

/// An [`Op`] with its binding precedences.
///
///
#[derive(Copy, Clone)]
pub struct OpInfo {
    /// The `Op`.
    pub op: Op,

    /// How tightly `op` binds to its operands.
    pub precedence: Precedence,
}

impl OpInfo {
    const fn nonfix(op: Op) -> Self { Self {op, precedence: Precedence::None} }
    const fn prefix(op: Op) -> Self { Self {op, precedence: Precedence::Prefix} }
    const fn infix(op: Op, precedence: Precedence) -> Self { Self {op, precedence} }
}

impl fmt::Debug for OpInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.op.fmt(f) }
}

/// Describes one of Welly's operator keywords. See also [`Op`].
///
/// In general, operators have two meanings. For example `-` can mean
/// negation or subtraction. The cases are distinguished according to whether
/// the operator is preceded by an expression.
///
/// If the operator has only one meaning, we put it in both slots.
#[derive(Copy, Clone)]
pub struct OpWord {
    /// The meaning of the operator if has a left operand.
    pub with_left: OpInfo,

    /// The meaning of the operator if has no left operand.
    pub without_left: OpInfo,
}

impl OpWord {
    /// Make an `OpWord` describing an operator that has two meanings.
    pub const fn new_pun(with_left: OpInfo, without_left: OpInfo) -> Self {
        Self {with_left, without_left }
    }

    /// Make an `OpWord` describing an operator that has one meaning.
    pub const fn new(op: OpInfo) -> Self { Self::new_pun(op, op) }
}

impl fmt::Debug for OpWord {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.with_left.fmt(f) }
}

impl PartialEq for OpWord {
    fn eq(&self, other: &Self) -> bool { self.with_left.op == other.with_left.op }
}

/// All [`OpWord`]s that exist in Welly.
pub const ALL_OP_WORDS: [(&'static str, OpWord); 37] = [
    ("true", OpWord::new(OpInfo::nonfix(Op::True))),
    ("false", OpWord::new(OpInfo::nonfix(Op::False))),
    ("Self", OpWord::new(OpInfo::nonfix(Op::SelfType))),
    ("or", OpWord::new(OpInfo::infix(Op::Or, Precedence::Or))),
    ("and", OpWord::new(OpInfo::infix(Op::And, Precedence::And))),
    ("not", OpWord::new(OpInfo::prefix(Op::Not))),
    ("in", OpWord::new(OpInfo::infix(Op::In, Precedence::In))),
    ("==", OpWord::new(OpInfo::infix(Op::EQ, Precedence::Eq))),
    ("!=", OpWord::new(OpInfo::infix(Op::NE, Precedence::Eq))),
    ("<", OpWord::new(OpInfo::infix(Op::SLT, Precedence::Cmp))),
    ("<+", OpWord::new(OpInfo::infix(Op::ULT, Precedence::Cmp))),
    (">", OpWord::new(OpInfo::infix(Op::SGT, Precedence::Cmp))),
    (">+", OpWord::new(OpInfo::infix(Op::UGT, Precedence::Cmp))),
    ("<=", OpWord::new(OpInfo::infix(Op::SLE, Precedence::Cmp))),
    ("<=+", OpWord::new(OpInfo::infix(Op::ULE, Precedence::Cmp))),
    (">=", OpWord::new(OpInfo::infix(Op::SGE, Precedence::Cmp))),
    (">=+", OpWord::new(OpInfo::infix(Op::UGE, Precedence::Cmp))),
    ("<>", OpWord::new(OpInfo::infix(Op::LG, Precedence::Cmp))),
    ("..", OpWord::new(OpInfo::infix(Op::Exclusive, Precedence::Range))),
    ("...", OpWord::new(OpInfo::infix(Op::Inclusive, Precedence::Range))),
    (":", OpWord::new(OpInfo::infix(Op::Cast, Precedence::Cast))),
    ("<<", OpWord::new(OpInfo::infix(Op::SL, Precedence::Shift))),
    (">>", OpWord::new(OpInfo::infix(Op::SSR, Precedence::Shift))),
    (">>+", OpWord::new(OpInfo::infix(Op::USR, Precedence::Shift))),
    ("+", OpWord::new_pun(OpInfo::infix(Op::Add, Precedence::Sum), OpInfo::prefix(Op::Plus))),
    ("-", OpWord::new_pun(OpInfo::infix(Op::Sub, Precedence::Sum), OpInfo::prefix(Op::Minus))),
    ("*", OpWord::new_pun(OpInfo::infix(Op::Mul, Precedence::Product), OpInfo::prefix(Op::Clone))),
    ("/", OpWord::new(OpInfo::infix(Op::SDiv, Precedence::Product))),
    ("/+", OpWord::new(OpInfo::infix(Op::UDiv, Precedence::Product))),
    ("%", OpWord::new(OpInfo::infix(Op::SRem, Precedence::Product))),
    ("%+", OpWord::new(OpInfo::infix(Op::URem, Precedence::Product))),
    ("|", OpWord::new(OpInfo::infix(Op::Union, Precedence::Union))),
    ("&", OpWord::new(OpInfo::prefix(Op::Lend))),
    ("$", OpWord::new(OpInfo::prefix(Op::Share))),
    ("struct", OpWord::new(OpInfo::prefix(Op::Structure))),
    ("^", OpWord::new(OpInfo::infix(Op::Power, Precedence::Power))),
    (".", OpWord::new(OpInfo::infix(Op::Dot, Precedence::Dot))),
];

// ----------------------------------------------------------------------------

/// All assignment operator keywords that exist in Welly.
pub const ALL_ASSIGN_WORDS: [(&'static str, Option<Op>); 12] = [
    ("=", None),
    ("<<=", Some(Op::SL)),
    (">>=", Some(Op::SSR)),
    (">>+=", Some(Op::USR)),
    ("+=", Some(Op::Add)),
    ("-=", Some(Op::Sub)),
    ("*=", Some(Op::Mul)),
    ("/=", Some(Op::SDiv)),
    ("/+=", Some(Op::UDiv)),
    ("%=", Some(Op::SRem)),
    ("%+=", Some(Op::URem)),
    ("^=", Some(Op::Power)),
];

// ----------------------------------------------------------------------------

/// A keyword that introduces an item.
#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
pub enum ItemWord {
    /// `mod name;` defines a module from a source file.
    ///
    /// `mod name { ... }` defines a module inline.
    Module,

    /// `obj name(...) { ... }` defines an object type.
    Object,

    /// `fn name(...): ... { ... }` defines a compiled method.
    Function,

    /// `macro name(...) { ... }` defines a dynamic method.
    Macro,

    /// `trait name { ... }` defines a trait.
    Trait,

    /// `impl name { ... }` implements a trait.
    Implementation,

    /// `return expr;` returns the value of the expression to the caller.
    Return,

    /// `match expr;` jumps down to the next `case` whose pattern matches the
    /// value of `expr`.
    Match,

    /// `case pattern { ... }` intercepts earlier `match`es whose expression
    /// has a value that matches `pattern`. The names in the pattern are bound
    /// to the fields of the value, then the block is executed.
    Case,

    /// `if expr { ... }` executes the block if the value of the expression is
    /// `true`.
    If,

    /// `while expr { ... }` executes the block repeatedly as long as the
    /// value of the expression is `true`.
    While,

    /// `for pattern in expr { ... }` makes an iterator from the expression,
    /// then, for each value the iterator yields, the names in the pattern are
    /// bound to the fields of the value, and the block is executed.
    ///
    /// Note that `pattern in expr` parses as a single expression.
    For,

    /// `else { ... }` must come after an `if`, `for` or `while`. It executes
    /// the block if the `if` expression is `false` or if the loop exits
    /// normally.
    Else,
}

/// All [`ItemWord`]s that exist in Welly.
pub const ALL_ITEM_WORDS: [(&'static str, ItemWord); 13] = [
    ("mod", ItemWord::Module),
    ("obj", ItemWord::Object),
    ("fn", ItemWord::Function),
    ("macro", ItemWord::Macro),
    ("trait", ItemWord::Trait),
    ("impl", ItemWord::Implementation),
    ("return", ItemWord::Return),
    ("match", ItemWord::Match),
    ("case", ItemWord::Case),
    ("if", ItemWord::If),
    ("while", ItemWord::While),
    ("for", ItemWord::For),
    ("else", ItemWord::Else),
];

// ----------------------------------------------------------------------------
