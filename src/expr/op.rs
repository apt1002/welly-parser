/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(u8);

impl Precedence {
    pub const MIN: Self = Precedence(0);
    pub const MAX: Self = Precedence(34);
}

/// An primitive arithmetic operation.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    /// `OK(x)?` is `x`; `ERR(x)?` returns `ERR(x)`.
    Query,

    /// `-7 ** 2` is `49`.
    Pow,

    /// `&x` is borrowed; `$x` is shared; `*x` is a fresh copy of `x`.
    Borrow, Share, Clone,

    /// `+ 3` is `3`; `- 3` is `-3`.
    Plus, Minus,

    /// `-7 * 2` is `-14`; `-7 / 2` is `-4`; `-7 % 2` is `1`.
    Mul, Div, Rem,

    /// `3 + 5` is `8`; `3 - 5` is `-2`.
    Add, Sub,

    /// `-7 << 2` is `-28`; `-7 >> 2` is `-2`, `-7 >>> 2` is `(1 << 62) - 2`.
    SL, ASR, LSR,

    /// `3 | 5` is `7`; `3 ^ 5` is `6`; `3 & 5` is `1`; `~3` is `-4`.
    BitOr, BitXor, BitAnd, BitNot,

    /// `x: t` - A value `x` cast to a type `t`.
    Cast,

    /// `0..3` means `0, 1, 2` and `0...3` means `0, 1, 2, 3`.
    Exclusive, Inclusive,

    /// All of `3 < 5`, `5 > 3`, `3 <= 5`, `5 >= 3` and `3 <> 5` are `true`.
    LT, GT, LE, GE, LG,

    /// `3 == 5` is `false`; `3 != 5` is `true`.
    EQ, NE,

    /// `item in collection` - Membership test.
    ///
    /// Also abused as part of `for item in collection { ... }`.
    In,

    /// `false or true` is `true`; `false and true` is `false`;
    /// `not false` is `true`.
    BoolOr, BoolAnd, BoolNot,

    /// Used when two expressions are juxtaposed. Always an error.
    Missing,
}

impl Op {
    /// Returns the left and right [`Precedence`] of `self`.
    ///
    /// Differences from Rust and Python:
    /// - `x in low .. high and b` means `(x in (low .. high)) and b`.
    ///   In Rust, there is no `in`.
    ///   `low .. high && b` means `low .. (high && b)`.
    ///   In Python, `:` is part of array subscription.
    ///   `a[x in low : high and b]` means `a[(x in low) : (high and b)]`.
    ///
    /// Differences from C, Java and Javascript:
    /// - `x & 1 == 0` means `(x & 1) == 0`.
    ///   In C, Java and Javascript it means `x & (1 == 0)`.
    /// - `-x ** 2` means `-(x ** 2)`
    ///   In Javascript it means `(-x) ** 2`.
    pub const fn precedence(self) -> (Option<Precedence>, Option<Precedence>) {
        const fn p(n: u8) -> Option<Precedence> { Some(Precedence(n)) }
        use Op::*;
        match self {
            Query => (p(34), None),
            Pow => (p(32), p(33)),
            BitNot | Plus | Minus | Borrow | Share | Clone => (None, p(30)),
            Mul | Div | Rem => (p(29), p(28)),
            Add | Sub => (p(27), p(26)),
            SL | ASR | LSR => (p(24), p(25)),
            BitAnd => (p(23), p(22)),
            BitXor => (p(21), p(20)),
            BitOr => (p(19), p(18)),
            Cast => (p(16), p(17)),
            Exclusive | Inclusive => (p(15), p(14)),
            LT | GT | LE | GE | LG => (p(13), p(12)),
            EQ | NE => (p(11), p(10)),
            In => (p(9), p(8)),
            BoolNot => (None, p(6)),
            BoolAnd => (p(5), p(4)),
            BoolOr => (p(3), p(2)),
            Missing => (p(1), p(0)),
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
