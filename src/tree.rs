use std::any::{Any};
use std::{fmt};

pub trait AsAny: Any {
    fn as_any(&self) -> &dyn Any;
    fn to_any(self: Box<Self>) -> Box<dyn Any>;
}

impl<T: Any> AsAny for T {
    fn as_any(&self) -> &dyn Any { self }
    fn to_any(self: Box<Self>) -> Box<dyn Any> { self }
}

// ----------------------------------------------------------------------------

/// A type that represents a parse tree.
pub trait Tree: fmt::Debug + AsAny {
    /// `declare()` all the keywords whose parse trees are `Self`s.
    fn declare_keywords(#[allow(unused)] declare: impl FnMut(&'static str, Self)) where Self: Sized {}
}

impl dyn Tree {
    pub fn is<T: Tree>(&self) -> bool { self.as_any().is::<T>() }

    pub fn downcast_ref<T: Tree>(&self) -> Option<&T> { self.as_any().downcast_ref::<T>() }

    pub fn downcast<T: Tree>(self: Box<Self>) -> Result<Box<T>, Box<Self>> {
        if (*self).is::<T>() {
            // Annoying that we have to check the type a second time.
            // However, this second check must not fail, otherwise we will have
            // a `dyn Any` that we can't turn back into a `dyn Tree`.
            Ok(self.to_any().downcast::<T>().unwrap())
        } else {
            Err(self)
        }
    }
}

impl Tree for () {}
impl Tree for char {}

// ----------------------------------------------------------------------------

/// Represents the end of the source code.
///
/// Parsers must return this [`Tree`] unchanged. It must never be incorporated
/// into a larger [`Tree`].
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct EndOfFile;

impl Tree for EndOfFile {}

