use super::{wm, Location, Loc, Locate, enums, lexer, parser};

// ----------------------------------------------------------------------------

/// Construct `Self` from `T` or report errors.
pub trait Validate<T: ?Sized>: Sized {
    fn validate(tree: &T) -> wm::Result<Self>;
}

impl<T, V: Validate<T>> Validate<Option<T>> for Option<V> {
    fn validate(tree: &Option<T>) -> wm::Result<Self> {
        Ok(if let Some(tree) = tree { Some(V::validate(&tree)?) } else { None })
    }
}

impl<T, V: Validate<T>> Validate<Loc<T>> for Loc<V> {
    fn validate(tree: &Loc<T>) -> wm::Result<Self> { Ok(Loc(V::validate(&tree.0)?, tree.1)) }
}

impl<T, V: Validate<[T]>> Validate<Box<[T]>> for V {
    fn validate(tree: &Box<[T]>) -> wm::Result<Self> { Ok(V::validate(&**tree)?) }
}

// ----------------------------------------------------------------------------

mod name;
pub use name::{Name, Tag};

mod stmt;
pub use stmt::{Stmt, Block};

mod expr;
pub use expr::{Expr, Selector};

mod pattern;
pub use pattern::{Mode, Pattern, RefutablePattern};
