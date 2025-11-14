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

impl Location {
    /// A dummy value that can be used for things like [`EndOfFile`].
    pub const EVERYWHERE: Location = Location {start: usize::MIN, end: usize::MAX};
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

impl<U, T: PartialEq<U>> PartialEq<U> for Loc<T> {
    fn eq(&self, other: &U) -> bool { self.0 == *other }
}

// ----------------------------------------------------------------------------

/// A list of [`Loc<T>`]s.
#[derive(Debug, Clone)]
pub struct List<T>(Box<[Loc<T>]>);

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().zip(other.0.iter()).all(|(t1, t2)| t1.0 == t2.0)
    }
}

