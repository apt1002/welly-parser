use super::{Location};

/// The error type of [`AST::validate()`].
///
/// This can conveniently be returned using the idoim `Err(report(...))?`.
pub struct Invalid;

impl From<()> for Invalid {
    fn from(_: ()) -> Self { Self }
}

/// Represents a valid abstract syntax tree of some valid Welly source code.
pub trait AST: Sized {
    /// The parser type that turns into `Self`.
    type Generous;

    /// Attempt to construct a `Self` given its parse tree.
    ///
    /// If you return `Invalid`, you must first `report()` at least one error.
    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid>;
}

impl<T: AST> AST for Option<T> {
    type Generous = Option<T::Generous>;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(if let Some(tree) = tree {
            Some(T::validate(report, tree)?)
        } else {
            None
        })
    }
}

impl<T: AST> AST for Box<T> {
    type Generous = Box<T::Generous>;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(Box::new(T::validate(report, tree)?))
    }
}
