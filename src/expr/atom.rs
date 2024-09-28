use super::{Tree, Op};

/// Describes one of the built-in operators.
///
/// In general, operators have two meanings. For example `'-'` can mean
/// negation or subtraction. The cases are distinguished according to whether
/// the operator is preceded by an expression.
///
/// If the operator has only one meaning, we put it in both slots.
#[derive(Debug, Copy, Clone)]
pub struct Operator {
    /// The meaning of the operator if has a left operand.
    pub with_left: Op,

    /// The meaning of the operator if has no left operand.
    pub without_left: Op,
}

impl Operator {
    /// Make an `Operator` describing an operator that has two meanings.
    pub const fn new_ambiguous(with_left: Op, without_left: Op) -> Self {
        Self {with_left, without_left }
    }

    /// Make an `Operator` describing an operator that has one meaning.
    pub const fn new(op: Op) -> Self { Self::new_ambiguous(op, op) }
}

impl Tree for Operator {
    fn declare_keywords(mut declare: impl FnMut(&'static str, Self)) {
        declare(":", Operator::new(Op::Cast));
        declare("..", Operator::new(Op::Exclusive));
        declare("...", Operator::new(Op::Inclusive));
        declare("or", Operator::new(Op::BoolOr));
        declare("and", Operator::new(Op::BoolAnd));
        declare("not", Operator::new(Op::BoolNot));
        declare("|", Operator::new(Op::BitOr));
        declare("^", Operator::new(Op::BitXor));
        declare("&", Operator::new_ambiguous(Op::BitAnd, Op::Borrow));
        declare("==", Operator::new(Op::EQ));
        declare("!=", Operator::new(Op::NE));
        declare("<", Operator::new(Op::LT));
        declare(">", Operator::new(Op::GT));
        declare("<=", Operator::new(Op::LE));
        declare(">=", Operator::new(Op::GE));
        declare("<>", Operator::new(Op::LG));
        declare("<<", Operator::new(Op::SL));
        declare(">>", Operator::new(Op::ASR));
        declare(">>>", Operator::new(Op::LSR));
        declare("+", Operator::new_ambiguous(Op::Add, Op::Plus));
        declare("-", Operator::new_ambiguous(Op::Sub, Op::Minus));
        declare("*", Operator::new_ambiguous(Op::Mul, Op::Clone));
        declare("/", Operator::new(Op::Div));
        declare("%", Operator::new(Op::Rem));
        declare("**", Operator::new(Op::Pow));
        declare("~", Operator::new(Op::BitNot));
        declare("$", Operator::new(Op::Share));
        declare("?", Operator::new(Op::Query));
    }
}
