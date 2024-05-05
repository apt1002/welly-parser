use std::{io};
use io::{Read};
use std::ops::{Range};
use super::{Location, Error, Result};

// ----------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Token<T> {
    pub loc: Location,
    pub token: T,
}

// ----------------------------------------------------------------------------

pub trait Stream<T> {
    /// Returns the next `T`, if any, without consuming it.
    /// The next call to `take` will return the same value.
    fn peek(&mut self) -> Result<&T>;

    /// Consumes and returns the next `T`, if any.
    fn take(&mut self) -> Result<Token<T>>;
}

// ----------------------------------------------------------------------------

pub struct Bytes<R: Read> {
    /// The underlying `Read`.
    input: R,
    /// The part of `buf` holding the remaining bytes from the latest `read()`.
    buf_range: Range<usize>,
    /// The total length of all previous `read()`s (not including the latest).
    stream_index: usize,
    /// Used to `read()`. `buf[buf_range]` is meaningful.
    buf: [u8; 0x1000],
}

impl<R: Read> Bytes<R> {
    fn new(input: R) -> Self {
        Bytes {
            input,
            buf_range: 0..0,
            stream_index: 0,
            buf: [0; 0x1000],
        }
    }

    /// If `buf_range` is empty, calls `read()` until it is not interrupted.
    /// Returns `Ok` if it manages to make `buf_range` non-empty.
    fn fill(&mut self) -> Result<()> {
        if !self.buf_range.is_empty() { return Ok(()); }
        self.stream_index += self.buf_range.end;
        loop { match self.input.read(&mut self.buf) {
            Ok(size) => {
                if size == 0 { return Err(Error::End); }
                self.buf_range = 0..size;
                return Ok(());
            },
            Err(error) => {
                if !matches!(error.kind(), io::ErrorKind::Interrupted) {
                    return Err(Error::IO(error));
                }
            },
        }}
    }
}

impl<R: Read> Stream<u8> for Bytes<R> {
    fn peek(&mut self) -> Result<&u8> {
        self.fill()?;
        Ok(&self.buf[self.buf_range.start])
    }

    fn take(&mut self) -> Result<Token<u8>> {
        self.fill()?;
        let buf_index = self.buf_range.next().unwrap();
        let loc = Location::from(self.stream_index + buf_index);
        let token = self.buf[buf_index];
        Ok(Token {loc, token})
    }
}
