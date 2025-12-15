use std::{fmt};
use std::num::{NonZeroU8};

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
    /// `structure.field` extracts the `field` component of `structure`.
    Dot,

    /// `(-7) ^ 2` is `49`.
    Pow,

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

    /// `3 + 5` is `8`.
    Add,

    /// `3 - 5` is `-2`.
    Sub,

    /// `-7 << 3` is `-28`.
    SL,

    /// `-7 >> 2` is `-2`.
    SSR,

    /// `-7 >>+ 2` is `0xFFFFFFFFFFFFFFFE`.
    USR,

    /// `x: t` - A value `x` cast to a type `t`.
    Cast,

    /// `0..3` means `0, 1, 2`.
    Exclusive,

    /// `0...3` means `0, 1, 2, 3`.
    Inclusive,

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

    /// `-3 == 5` is `false`.
    EQ,

    /// `-3 != 5` is `true`.
    NE,

    /// `item in collection` - Membership test.
    ///
    /// Also abused as part of `for item in collection { ... }`.
    In,

    /// `not false` is `true`.
    Not,

    /// `false and true` is `false`.
    And,

    /// `false or true` is `true`.
    Or,

    /// The value `true`.
    True,

    /// The value `false`.
    False,

    /// The value `self`.
    SelfValue,

    /// The type `Self`.
    SelfType,
}

// ----------------------------------------------------------------------------

/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(NonZeroU8);

impl Precedence {
    pub const MIN: Self = Precedence(NonZeroU8::new(1).unwrap());
}

const fn p(n: u8) -> Option<Precedence> { Some(Precedence(NonZeroU8::new(n).unwrap())) }

/// An [`Op`] with its binding precedences.
///
///
#[derive(Copy, Clone)]
pub struct OpInfo {
    /// The `Op`.
    pub op: Op,

    /// How tightly `op` binds to its left operand, if any.
    pub left: Option<Precedence>,

    /// How tightly `op` binds to its right operand, if any.
    pub right: Option<Precedence>,
}

impl OpInfo {
    const fn nonfix(op: Op) -> Self { Self {op, left: None, right: None} }
    const fn prefix(op: Op, right: u8) -> Self { Self {op, left: None, right: p(right)} }
    const fn infix_left(op: Op, left: u8) -> Self { Self {op, left: p(left), right: p(left+1)} }
    const fn infix_right(op: Op, right: u8) -> Self { Self {op, left: p(right+1), right: p(right)} }
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
    pub const fn new_ambiguous(with_left: OpInfo, without_left: OpInfo) -> Self {
        Self {with_left, without_left }
    }

    /// Make an `OpWord` describing an operator that has one meaning.
    pub const fn new(op: OpInfo) -> Self { Self::new_ambiguous(op, op) }
}

impl fmt::Debug for OpWord {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.with_left.fmt(f) }
}

impl PartialEq for OpWord {
    fn eq(&self, other: &Self) -> bool { self.with_left.op == other.with_left.op }
}

/// All [`OpWord`]s that exist in Welly.
pub const ALL_OP_WORDS: [(&'static str, OpWord); 37] = [
    (".", OpWord::new(OpInfo::infix_left(Op::Dot, 30))),
    ("^", OpWord::new(OpInfo::infix_right(Op::Pow, 28))),
    ("|", OpWord::new(OpInfo::infix_left(Op::Union, 26))),
    ("&", OpWord::new(OpInfo::prefix(Op::Lend, 24))),
    ("$", OpWord::new(OpInfo::prefix(Op::Share, 24))),
    ("*", OpWord::new_ambiguous(OpInfo::infix_left(Op::Mul, 22), OpInfo::prefix(Op::Clone, 24))),
    ("/", OpWord::new(OpInfo::infix_left(Op::SDiv, 22))),
    ("/+", OpWord::new(OpInfo::infix_left(Op::UDiv, 22))),
    ("%", OpWord::new(OpInfo::infix_left(Op::SRem, 22))),
    ("%+", OpWord::new(OpInfo::infix_left(Op::URem, 22))),
    ("+", OpWord::new_ambiguous(OpInfo::infix_left(Op::Add, 20), OpInfo::prefix(Op::Plus, 24))),
    ("-", OpWord::new_ambiguous(OpInfo::infix_left(Op::Sub, 20), OpInfo::prefix(Op::Minus, 24))),
    ("<<", OpWord::new(OpInfo::infix_right(Op::SL, 18))),
    (">>", OpWord::new(OpInfo::infix_right(Op::SSR, 18))),
    (">>+", OpWord::new(OpInfo::infix_right(Op::USR, 18))),
    (":", OpWord::new(OpInfo::infix_right(Op::Cast, 16))),
    ("..", OpWord::new(OpInfo::infix_left(Op::Exclusive, 14))),
    ("...", OpWord::new(OpInfo::infix_left(Op::Inclusive, 14))),
    ("<", OpWord::new(OpInfo::infix_left(Op::SLT, 12))),
    ("<+", OpWord::new(OpInfo::infix_left(Op::ULT, 12))),
    (">", OpWord::new(OpInfo::infix_left(Op::SGT, 12))),
    (">+", OpWord::new(OpInfo::infix_left(Op::UGT, 12))),
    ("<=", OpWord::new(OpInfo::infix_left(Op::SLE, 12))),
    ("<=+", OpWord::new(OpInfo::infix_left(Op::ULE, 12))),
    (">=", OpWord::new(OpInfo::infix_left(Op::SGE, 12))),
    (">=+", OpWord::new(OpInfo::infix_left(Op::UGE, 12))),
    ("<>", OpWord::new(OpInfo::infix_left(Op::LG, 12))),
    ("==", OpWord::new(OpInfo::infix_left(Op::EQ, 10))),
    ("!=", OpWord::new(OpInfo::infix_left(Op::NE, 10))),
    ("in", OpWord::new(OpInfo::infix_left(Op::In, 8))),
    ("not", OpWord::new(OpInfo::prefix(Op::Not, 6))),
    ("and", OpWord::new(OpInfo::infix_left(Op::And, 4))),
    ("or", OpWord::new(OpInfo::infix_left(Op::Or, 2))),
    ("true", OpWord::new(OpInfo::nonfix(Op::True))),
    ("false", OpWord::new(OpInfo::nonfix(Op::False))),
    ("self", OpWord::new(OpInfo::nonfix(Op::SelfValue))),
    ("Self", OpWord::new(OpInfo::nonfix(Op::SelfType))),
];

// ----------------------------------------------------------------------------

/// All assignment operator keywords that exist in Welly.
pub const ALL_ASSIGN_WORDS: [(&'static str, Option<Op>); 12] = [
    ("=", None),
    ("^=", Some(Op::Pow)),
    ("*=", Some(Op::Mul)),
    ("/=", Some(Op::SDiv)),
    ("/+=", Some(Op::UDiv)),
    ("%=", Some(Op::SRem)),
    ("%+=", Some(Op::URem)),
    ("+=", Some(Op::Add)),
    ("-=", Some(Op::Sub)),
    ("<<=", Some(Op::SL)),
    (">>=", Some(Op::SSR)),
    (">>+=", Some(Op::USR)),
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
