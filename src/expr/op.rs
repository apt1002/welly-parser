/// Represents the binding precedence of an operator.
/// No left-`Precedence` is ever equal to a right-`Precedence`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(u8);

impl Precedence {
    pub const MIN: Self = Precedence(0);
    pub const MAX: Self = Precedence(29);
}

/// Represents one of Welly's arithmetic operations. See also [`Operator`].
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
/// [`Operator`]: super::Operator
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    // TODO: `when`.
    // TODO: `.`.

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

    /// Used when two expressions are juxtaposed. Always an error.
    Missing,
}

impl Op {
    /// Returns the left and right [`Precedence`] of `self`.
    ///
    /// Differences from Rust and Python:
    /// - `x in low .. high and b` means `(x in (low .. high)) and b`.
    ///   - In Rust, `low .. high && b` means `low .. (high && b)`.
    ///   - In Python, `a[x in low : high and b]` means
    ///     `a[(x in low) : (high and b)]`.
    ///
    /// Differences from C, Java and Javascript:
    /// - `-x ^ 2` means `-(x ^ 2)`, i.e. minus `x` squared.
    ///   - In Javascript, '^' is spelt '**', and `-x ** 2` means `(-x) ** 2`.
    pub const fn precedence(self) -> (Option<Precedence>, Option<Precedence>) {
        const fn p(n: u8) -> Option<Precedence> { Some(Precedence(n)) }
        use Op::*;
        match self {
            Pow => (p(28), p(29)),
            Union => (p(27), p(26)),
            Plus | Minus | Lend | Share | Clone => (None, p(24)),
            Mul | SDiv | UDiv | SRem | URem => (p(23), p(22)),
            Add | Sub => (p(21), p(20)),
            SL | SSR | USR => (p(18), p(19)),
            Cast => (p(16), p(17)),
            Exclusive | Inclusive => (p(15), p(14)),
            SLT | ULT | SGT | UGT | SLE | ULE | SGE | UGE | LG => (p(13), p(12)),
            EQ | NE => (p(11), p(10)),
            In => (p(9), p(8)),
            Not => (None, p(6)),
            And => (p(5), p(4)),
            Or => (p(3), p(2)),
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
        let (_, right) = Op::Pow.precedence();
        assert_eq!(right.unwrap(), Precedence::MAX);
    }
}
