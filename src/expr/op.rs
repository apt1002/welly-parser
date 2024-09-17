/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(u8);

impl Precedence {
    pub const MIN: Self = Precedence(0);
    pub const MAX: Self = Precedence(29);
}

/// An arithmetic operation.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    /// Used when two expressions are juxtaposed. Always an error.
    Missing,

    /// `x: t` - A value `x` cast to a type `t`.
    Cast,

    /// `0..3` means `0, 1, 2` and `0...3` means `0, 1, 2, 3`.
    Exclusive, Inclusive,

    /// `false or true` is `true`; `false and true` is `false`;
    /// `not false` is `true`.
    BoolOr, BoolAnd, BoolNot,

    /// `3 | 5` is `7`; `3 ^ 5` is `6`; `3 & 5` is `1`; `~3` is `-4`.
    BitOr, BitXor, BitAnd, BitNot,

    /// `3 == 5` is `false`; `3 != 5` is `true`.
    EQ, NE,

    /// All of `3 < 5`, `5 > 3`, `3 <= 5`, `5 >= 3` and `3 <> 5` are `true`.
    LT, GT, LE, GE, LG,

    /// `-7 << 2` is `-28`; `-7 >> 2` is `-2`, `-7 >>> 2` is `(1 << 62) - 2`.
    SL, ASR, LSR,

    /// `3 + 5` is `8`; `3 - 5` is `-2`.
    Add, Sub,

    /// `-7 * 2` is `-14`; `-7 / 2` is `-4`; `-7 % 2` is `1`.
    Mul, Div, Rem,

    /// `-7 ** 2` is `49`.
    Pow,

    /// `+ 3` is `3`; `- 3` is `-3`.
    Plus, Minus,

    /// `&x` is borrowed; `$x` is shared; `*x` is a fresh copy of `x`.
    Borrow, Share, Clone,

    /// `OK(x)?` is `x`; `ERR(x)?` returns `ERR(x)`.
    Query,
}

impl Op {
    /// Returns the left and right [`Precedence`] of `self`.
    pub const fn precedence(self) -> (Option<Precedence>, Option<Precedence>) {
        const fn p(n: u8) -> Option<Precedence> { Some(Precedence(n)) }
        use Op::*;
        match self {
            Missing => (p(1), p(0)),
            Cast => (p(2), p(3)),
            Exclusive | Inclusive => (p(5), p(4)),
            BoolOr => (p(7), p(6)),
            BoolAnd => (p(9), p(8)),
            BoolNot => (None, p(8)),
            BitOr => (p(11), p(10)),
            BitXor => (p(13), p(12)),
            BitAnd => (p(15), p(14)),
            EQ | NE => (p(17), p(16)),
            LT | GT | LE | GE | LG => (p(19), p(18)),
            SL | ASR | LSR => (p(20), p(21)),
            Add | Sub => (p(23), p(22)),
            Mul | Div | Rem => (p(25), p(24)),
            Pow => (p(26), p(27)),
            BitNot | Plus | Minus | Borrow | Share | Clone => (None, p(28)),
            Query => (p(29), None),
        }
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn limits() {
        let (_, right) = Op::Missing.precedence();
        assert_eq!(right.unwrap(), Precedence::MIN);
        let (left, _) = Op::Query.precedence();
        assert_eq!(left.unwrap(), Precedence::MAX);
    }
}
