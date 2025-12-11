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

    /// Apply `f` to the `T`.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Loc<U> { Loc(f(self.0), self.1) }
}

impl<T: fmt::Debug> fmt::Debug for Loc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)?;
        write!(f, " ({:?})", self.1)
    }
}

// ----------------------------------------------------------------------------

/// A list of [`Loc<T>`]s.
#[derive(Clone)]
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

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl<T, U> From<U> for List<T> where Box<[Loc<T>]>: From<U> {
    fn from(value: U) -> Self { Self(value.into()) }
}

// ----------------------------------------------------------------------------

/// Report a complicated error to the user.
pub trait Report {
    /// Report `self` by calling `log()` one or more times.
    fn report(&self, log: &mut dyn FnMut(&str, Option<Location>));
}

/// The type of errors with source-code locations.
pub enum Error {
    /// The parser treid to read beyond the end of the input.
    ///
    /// If the input is complete, this is an error.
    /// Otherwise it indicates that we need more input from the user.
    InsufficientInput,

    /// Many errors have a constant message and just one [`Location`].
    Str(&'static str, Location),

    /// Catch-all for complicated cases.
    Report(Box<dyn Report>),
}

impl Error {
    pub fn report(&self, mut log: impl FnMut(&str, Option<Location>)) {
        match self {
            Self::InsufficientInput => log("The program ends unexpectedly", None),
            Self::Str(message, loc) => log(message, Some(*loc)),
            Self::Report(e) => e.report(&mut log),
        }
    }
}

impl From<Loc<&'static str>> for Error {
    fn from(value: Loc<&'static str>) -> Self { Self::Str(value.0, value.1) }
}

impl<R: Report + 'static> From<R> for Error {
    fn from(value: R) -> Self { Self::Report(Box::new(value)) }
}
