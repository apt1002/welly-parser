use std::{fmt, io};
use std::ops::{Range};

/// A position in source code in a form that can be reported to the user.
/// More precisely, a `Location` represents a contiguous range of bytes of
/// source code.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The byte index where this `Location` begins.
    start: usize,
    /// The byte index following this `Location`.
    end: usize,
}

impl Location {
    /// Returns the smallest `Location` containing all
    fn union(pieces: &[Self]) -> Self {
        let mut pieces = pieces.iter().copied();
        let mut ret = pieces.next().expect("Cannot form the union of no pieces");
        while let Some(piece) = pieces.next() {
            ret.start = std::cmp::min(ret.start, piece.start);
            ret.end = std::cmp::min(ret.end, piece.end);
        }
        ret
    }
}

impl From<usize> for Location {
    fn from(value: usize) -> Self { Self {start: value, end: value + 1} }
}

impl From<(usize, usize)> for Location {
    fn from(value: (usize, usize)) -> Self { Self {start: value.0, end: value.1} }
}

impl From<Range<usize>> for Location {
    fn from(value: Range<usize>) -> Self { Self {start: value.start, end: value.end} }
}

// ----------------------------------------------------------------------------

/// Represents an error message referring to a position in source code.
#[derive(Debug)]
pub enum Error {
    /// No more input.
    End,
    /// An I/O error.
    IO(io::Error),
    /// A syntax error.
    Syntax(String, Location),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::End => { f.write_str("End of file") },
            Self::IO(error) => { error.fmt(f) },
            Self::Syntax(msg, _) => { f.write_str(msg) }
        }
    }
}

impl std::error::Error for Error {}

// ----------------------------------------------------------------------------

/// Return type of a function that parses a `T`.
pub type Result<T> = std::result::Result<T, Error>;
