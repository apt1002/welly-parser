use super::{Precedence, Op, Expr};

/// Represents an [`Op`] that is missing its right operand.
#[derive(Debug)]
pub struct Waiting {
    /// The left operand, if any.
    expr: Option<Box<Expr>>,

    /// The `Op`.
    op: Op,

    /// The right precedence of `Op`.
    right: Precedence,
}

/// Represents an alternating sequence of [`Expr`]s and [`Op`]s, starting
/// with an `Expr`.
///
/// Each `Op` has a left precedence higher than the right precedence of the
/// preceding `Op` (otherwise we can replace an `Expr` `Op` `Expr` sequence
/// with an [`Expr::Op`]).
#[derive(Default, Debug)]
pub struct Stack {
    /// A sequence of (`Expr`, `Op`) pairs.
    ops: Vec<Waiting>,

    /// The final `Expr`, if any.
    expr: Option<Box<Expr>>,
}

impl Stack {
    /// Tests whether the sequence ends with an [`Expr`].
    pub fn has_expr(&self) -> bool { self.expr.is_some() }

    /// Returns the right-precedence of the last `Op`.
    fn right(&self) -> Option<Precedence> { self.ops.last().map(|w| w.right) }

    /// Before beginning a new [`Expr`], ensure that `self.expr` is `None` by
    /// inserting an [`Op::Missing`] if necessary.
    fn insert_missing(&mut self) {
        let expr = self.expr.take();
        if expr.is_some() {
            // We have a left operand we weren't expecting.
            self.ops.push(Waiting {expr, op: Op::Missing, right: Precedence::MIN});
        }
    }

    /// Before appending something with left-precedence `left`, see if the
    /// preceding `Op`s have a higher right-precedence, and if so construct
    /// some `Expr::Op`s.
    fn partial_flush(&mut self, left: Precedence) {
        while let Some(right) = self.right() {
            if right < left { break }
            let Waiting {expr, op, ..} = self.ops.pop().unwrap();
            let expr = Expr::Op(expr, op, self.expr.take());
            self.expr = Some(Box::new(expr));
        }
    }

    /// Collapse this `Stack` down to a single [`Expr`], if non-empty.
    pub fn flush(mut self) -> Option<Box<Expr>> {
        let mut ret = self.expr;
        while let Some(Waiting {expr, op, ..}) = self.ops.pop() {
            ret = Some(Box::new(Expr::Op(expr, op, ret)));
        }
        ret
    }

    /// Append an [`Op`].
    ///
    /// `Op`s can be nonfix, prefix, postfix or infix.
    pub fn op(&mut self, op: Op) {
        let (left, right) = op.precedence();
        if let Some(left) = left {
            self.partial_flush(left);
        } else {
            self.insert_missing();
        }
        if let Some(right) = right {
            let expr = self.expr.take();
            self.ops.push(Waiting {expr, op, right});
        } else {
            let expr = Expr::Op(self.expr.take(), op, None);
            self.expr = Some(Box::new(expr));
        }
    }

    /// Append a non-[`Op`] that has no operands.
    pub fn nonfix(&mut self, nonfix: Expr) {
        self.insert_missing();
        self.expr = Some(Box::new(nonfix));
    }

    /// Append a non-[`Op`] that has a left operand.
    pub fn postfix(&mut self, left: Precedence, postfix: impl FnOnce(Option<Box<Expr>>) -> Expr) {
        self.partial_flush(left);
        let expr = postfix(self.expr.take());
        self.expr = Some(Box::new(expr));
    }
}
