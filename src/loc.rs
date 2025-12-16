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

impl std::ops::Add<usize> for Location {
    type Output = Self;

    fn add(self, rhs: usize) -> Self { Location {start: self.start + rhs, end: self.end + rhs} }
}

impl std::ops::Sub<usize> for Location {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self { Location {start: self.start - rhs, end: self.end - rhs} }
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

/// Find the [`Location`] of `Self`.
pub trait Locate {
    /// Returns a [`Location`] spanning the whole of `Self`.
    fn loc(&self) -> Location { Location{start: self.loc_start(), end: self.loc_end()} }

    /// Used to compute `self.loc().start`.
    fn loc_start(&self) -> usize;

    /// Used to compute `self.loc().end`.
    fn loc_end(&self) -> usize;
}

impl Locate for Location {
    fn loc(&self) -> Location { *self }
    fn loc_start(&self) -> usize { self.start }
    fn loc_end(&self) -> usize { self.end }
}

impl<T> Locate for Loc<T> {
    fn loc(&self) -> Location { self.1 }
    fn loc_start(&self) -> usize { self.1.start }
    fn loc_end(&self) -> usize { self.1.end }
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

    /// An error with a constant message and just one [`Location`].
    Str(&'static str, Location),

    /// A more complicated error.
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

// ----------------------------------------------------------------------------

/// An abbreviation.
pub type Result<T> = std::result::Result<T, Error>;
