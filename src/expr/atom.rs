use super::{Tree, Op};

/// Describes one of the built-in operators.
///
/// In general, operators have two meanings. For example `'-'` can mean
/// negation or subtraction. The cases are distinguished according to whether
/// the operator is preceded by an expression.
///
/// If the operator has only one meaning, we put it in both slots.
#[derive(Debug)]
pub struct Info {
    /// The textual representation of the operator.
    pub name: &'static str,

    /// The meaning of the operator if has a left operand.
    pub with_left: Op,

    /// The meaning of the operator if has no left operand.
    pub without_left: Op,
}

impl Info {
    /// Make an `Info` describing an operator that has two meanings.
    pub const fn new_ambiguous(name: &'static str, with_left: Op, without_left: Op) -> Self {
        Self {name, with_left, without_left }
    }

    /// Make an `Info` describing an operator that has one meaning.
    pub const fn new(name: &'static str, op: Op) -> Self { Self::new_ambiguous(name, op, op) }
}

pub const ALL_OPERATORS: &'static [Info] = &[
    Info::new(":", Op::Cast),
    Info::new("..", Op::Exclusive),
    Info::new("...", Op::Inclusive),
    Info::new("or", Op::BoolOr),
    Info::new("and", Op::BoolAnd),
    Info::new("not", Op::BoolNot),
    Info::new("|", Op::BitOr),
    Info::new("^", Op::BitXor),
    Info::new_ambiguous("&", Op::BitAnd, Op::Borrow),
    Info::new("==", Op::EQ),
    Info::new("!=", Op::NE),
    Info::new("<", Op::LT),
    Info::new(">", Op::GT),
    Info::new("<=", Op::LE),
    Info::new(">=", Op::GE),
    Info::new("<>", Op::LG),
    Info::new("<<", Op::SL),
    Info::new(">>", Op::ASR),
    Info::new(">>>", Op::LSR),
    Info::new_ambiguous("+", Op::Add, Op::Plus),
    Info::new_ambiguous("-", Op::Sub, Op::Minus),
    Info::new_ambiguous("*", Op::Mul, Op::Clone),
    Info::new("/", Op::Div),
    Info::new("%", Op::Rem),
    Info::new("**", Op::Pow),
    Info::new("~", Op::BitNot),
    Info::new("$", Op::Share),
    Info::new("?", Op::Query),
];

/// The parse tree of a built-in operator.
pub type Operator = &'static Info;

impl Tree for Operator {}
