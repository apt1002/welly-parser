use std::{fmt};

/// A position in source code in a form that can be reported to the user.
/// More precisely, a `Location` represents a contiguous range of bytes of
/// source code.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The byte index where this `Location` begins.
    pub start: usize,
    /// The byte index following this `Location`.
    pub end: usize,
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

// ----------------------------------------------------------------------------

/// Represents a `T` with a [`Location`].
///
/// This is commonly used to represent bits of a parse tree, remembering where
/// they came from in the source code.
#[derive(Copy, Clone)]
pub struct Loc<T>(pub T, pub Location);

impl<T> Loc<T> {
    /// Convert an `&Loc<T>` to a `Loc<&T>`.
    pub fn as_ref(&self) -> Loc<&T> { Loc(&self.0, self.1) }
}

impl<T: fmt::Debug> fmt::Debug for Loc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)?;
        write!(f, " ({:?})", self.1)
    }
}

// ----------------------------------------------------------------------------

/// A list of [`Loc<T>`]s.
#[derive(Debug, Clone)]
pub struct List<T>(Box<[Loc<T>]>);

impl<T> List<T> {
    /// Returns a [`Location`] encompassing the whole `List`,
    /// or `None` if the `List` is empty.
    pub fn loc(&self) -> Option<Location> {
        if self.0.len() == 0 { return None; }
        Some(Location {
            start: self.0.first().unwrap().1.start,
            end: self.0.last().unwrap().1.end,
        })
    }
}

impl<T, U> From<U> for List<T> where Box<[Loc<T>]>: From<U> {
    fn from(value: U) -> Self { Self(value.into()) }
}
