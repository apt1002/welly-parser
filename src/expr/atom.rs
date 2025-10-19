use super::{Tree, Op};

/// Describes one of Welly's built-in operators. See also [`Op`].
///
/// In general, operators have two meanings. For example `-` can mean
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
        declare("^", Operator::new(Op::Pow));
        declare("|", Operator::new(Op::Union));
        declare("&", Operator::new(Op::Lend));
        declare("$", Operator::new(Op::Share));
        declare("*", Operator::new_ambiguous(Op::Mul, Op::Clone));
        declare("/", Operator::new(Op::SDiv));
        declare("/+", Operator::new(Op::UDiv));
        declare("%", Operator::new(Op::SRem));
        declare("%+", Operator::new(Op::URem));
        declare("+", Operator::new_ambiguous(Op::Add, Op::Plus));
        declare("-", Operator::new_ambiguous(Op::Sub, Op::Minus));
        declare("<<", Operator::new(Op::SL));
        declare(">>", Operator::new(Op::SSR));
        declare(">>+", Operator::new(Op::USR));
        declare(":", Operator::new(Op::Cast));
        declare("..", Operator::new(Op::Exclusive));
        declare("...", Operator::new(Op::Inclusive));
        declare("<", Operator::new(Op::SLT));
        declare("<+", Operator::new(Op::ULT));
        declare(">", Operator::new(Op::SGT));
        declare(">+", Operator::new(Op::UGT));
        declare("<=", Operator::new(Op::SLE));
        declare("<=+", Operator::new(Op::ULE));
        declare(">=", Operator::new(Op::SGE));
        declare(">=+", Operator::new(Op::UGE));
        declare("<>", Operator::new(Op::LG));
        declare("==", Operator::new(Op::EQ));
        declare("!=", Operator::new(Op::NE));
        declare("in", Operator::new(Op::In));
        declare("not", Operator::new(Op::Not));
        declare("and", Operator::new(Op::And));
        declare("or", Operator::new(Op::Or));
    }
}
