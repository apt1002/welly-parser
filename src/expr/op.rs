/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(u8);

impl Precedence {
    pub const MIN: Self = Precedence(0);
    pub const MAX: Self = Precedence(34);
}

/// Represents one of Welly's arithmetic operations. See also [`Operator`].
///
/// [`Operator`]: super::Operator
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    /// `OK(x)?` is `x`; `ERR(x)?` returns `ERR(x)`.
    Query,

    /// `(-7) ** 2` is `49`.
    Pow,

    /// `~3` is `-4`.
    BitNot,

    /// `+3` is `3`.
    Plus,

    /// `-3` is `-3`.
    Minus,

    /// `&x` is borrowed.
    Borrow,

    /// `$x` is shared.
    Share,

    /// `*x` is a fresh copy of `x`.
    Clone,

    /// `-7 * 2` is `-14`.
    Mul,

    /// `-7 / 2` is `-4`.
    Div,

    /// `-7 % 2` is `1`.
    Rem,

    /// `3 + 5` is `8`.
    Add,

    /// `3 - 5` is `-2`.
    Sub,

    /// `-7 << 2` is `-28`.
    SL,

    /// `-7 >> 2` is `-2`.
    ASR,

    /// `-7 >>> 2` is `(1 << 62) - 2`.
    LSR,

    /// `3 & 5` is `1`.
    BitAnd,

    /// `3 ^ 5` is `6`.
    BitXor,

    /// `3 | 5` is `7`.
    BitOr,

    /// `x: t` - A value `x` cast to a type `t`.
    Cast,

    /// `0..3` means `0, 1, 2`.
    Exclusive,

    /// `0...3` means `0, 1, 2, 3`.
    Inclusive,

    /// `3 < 5` is true.
    LT,

    /// `5 > 3` is true.
    GT,

    /// `3 <= 5` is true.
    LE,

    /// `5 >= 3` is true.
    GE,

    /// `3 <> 5` is `true`.
    LG,

    /// `3 == 5` is `false`.
    EQ,

    /// `3 != 5` is `true`.
    NE,

    /// `item in collection` - Membership test.
    ///
    /// Also abused as part of `for item in collection { ... }`.
    In,

    /// `not false` is `true`.
    BoolNot,

    /// `false and true` is `false`.
    BoolAnd,

    /// `false or true` is `true`.
    BoolOr,

    /// Used when two expressions are juxtaposed. Always an error.
    Missing,
}

impl Op {
    /// Returns the left and right [`Precedence`] of `self`.
    ///
    /// Differences from Rust and Python:
    /// - `x in low .. high and b` means `(x in (low .. high)) and b`.
    ///   - In Rust, there is no `in`.
    ///     `low .. high && b` means `low .. (high && b)`.
    ///   - In Python, `:` is part of array subscription.
    ///     `a[x in low : high and b]` means `a[(x in low) : (high and b)]`.
    ///
    /// Differences from C, Java and Javascript:
    /// - `x & 1 == 0` means `(x & 1) == 0`.
    ///   - In C, Java and Javascript it means `x & (1 == 0)`.
    /// - `-x ** 2` means `-(x ** 2)`
    ///   - In Javascript it means `(-x) ** 2`.
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
