use std::any::{Any};
use std::{fmt};

/// Object-safe methods for turning `self` into `dyn Any`.
///
/// These are blanket-implemented for all [`Sized`] types.
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
///
/// There are many types that implement `Tree`. It would be inconvenient to
/// define an `enum` that can contain any of them. Instead, we use `dyn Tree`.
/// You can use the methods of `dyn Tree` to match its actual type:
///
/// ```
/// use welly_parser::{Tree};
///
/// // Invent a new kind of `Tree`.
/// #[derive(Debug)]
/// struct Fruit(&'static str);
/// impl Tree for Fruit {}
///
/// // An example `Fruit` wrapped as a `dyn Tree`.
/// let tree: Box<dyn Tree> = Box::new(Fruit("Apple"));
///
/// // Test whether `tree` is a `Fruit`.
/// let is_fruit: bool = tree.is::<Fruit>();
/// println!("{}", is_fruit);
///
/// // Borrow the `Fruit`.
/// let borrowed_fruit: Option<&Fruit> = tree.downcast_ref::<Fruit>();
/// println!("{}", borrowed_fruit.expect("Not a Fruit").0);
///
/// // Move the `Fruit`.
/// let owned_fruit: Result<Box<Fruit>, Box<dyn Tree>> = tree.downcast::<Fruit>();
/// println!("{}", owned_fruit.expect("Not a Fruit").0);
/// ```
pub trait Tree: fmt::Debug + AsAny {
    /// `declare()` all the keywords whose parse trees are `Self`s.
    ///
    /// The default implementation declares no keywords.
    fn declare_keywords(#[allow(unused)] declare: impl FnMut(&'static str, Self)) where Self: Sized {}
}

impl dyn Tree {
    /// Returns `true` if the actual type of `self` is `T`.
    pub fn is<T: Tree>(&self) -> bool { self.as_any().is::<T>() }

    /// Returns `Some` if the actual type of `self` is `T`.
    pub fn downcast_ref<T: Tree>(&self) -> Option<&T> { self.as_any().downcast_ref::<T>() }

    /// Returns `Ok` if the actual type of `self` is `T`.
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

impl<T: Tree + PartialEq> PartialEq<T> for dyn Tree {
    fn eq(&self, other: &T) -> bool {
        if let Some(tree) = self.downcast_ref::<T>() { tree == other } else { false }
    }
}

impl Tree for () {}
impl Tree for char {}

// ----------------------------------------------------------------------------

/// Represents the end of the source code.
///
/// Parsers must return this [`Tree`] unchanged. It must never be incorporated
/// into a larger `Tree`.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct EndOfFile;

impl Tree for EndOfFile {}

