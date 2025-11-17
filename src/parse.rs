use super::loc::{Location, Loc};

/// A stream of items.
pub trait Stream {
    /// The return type of `read()`.
    type Item;

    /// Read the next item, if any.
    fn read(&mut self) -> Option<Self::Item>;

    /// Unread `item`. The next call to `read()` will return `item`.
    ///
    /// # Panics
    ///
    /// If you `unread()` more than one item.
    fn unread(&mut self, item: Self::Item);

    /// Returns `true` if there are no more [`Self::Item`]s to `read()`.
    fn is_empty(&mut self) -> bool {
        if let Some(item) = self.read() {
            self.unread(item);
            false
        } else {
            true
        }
    }
}

impl<'a, S: Stream> Stream for &'a mut S {
    type Item = S::Item;
    fn read(&mut self) -> Option<Self::Item> { S::read(*self) }
    fn unread(&mut self, item: Self::Item) { S::unread(*self, item) }
    fn is_empty(&mut self) -> bool { S::is_empty(*self) }
}

// ----------------------------------------------------------------------------

/// A [`Stream`] implemented in terms of an [`Iterator`].
#[derive(Debug)]
struct IteratorStream<I: Iterator> {
    /// The underlying [`Iterator`].
    iter: I,

    /// Optionally, a value to return before fetching one from `iter`.
    item: Option<I::Item>,
}

impl<I: IntoIterator> From<I> for IteratorStream<I::IntoIter> {
    fn from(value: I) -> Self { Self {iter: value.into_iter(), item: None} }
}

impl<I: Iterator> Stream for IteratorStream<I> {
    type Item = I::Item;

    fn read(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.item.take() { return Some(item); }
        let Some(item) = self.iter.next() else { return None; };
        Some(item)
    }

    fn unread(&mut self, item: Self::Item) {
        assert!(self.item.is_none());
        self.item = Some(item);
    }
}

// ----------------------------------------------------------------------------

/// Parse a [`Stream`] of [`Self::Input`] to make a [`Self::Output`].
pub trait Parse {
    /// The item type of the stream parsed by `Self`.
    type Input;

    /// The successful return type of `parse_one()`.
    type Output;

    /// The unsuccessful return type of `parse_one()`.
    type Error;

    /// Attempt to parse one `T` from `input`.
    ///
    /// Returns:
    /// - Ok(None) - One or more useless [`Self::Input`]s were discarded.
    /// - Ok(Some(output)) - One or more [`Self::Input`]s was combined into a
    ///   `Self::Output`.
    /// - Err(None) - There were not enough [`Self::Input`]s to parse a `T`.
    /// - Err(Some(error)) - One or more invalid [`Self::Input`]s were
    ///   discarded.
    fn parse_one(&self, input: &mut impl Stream<Item=Self::Input>)
    -> Result<Option<Self::Output>, Option<Self::Error>>;

    /// Parse a sequence of [`Self::Input`] into a sequence of `T`, or return
    /// the first error.
    ///
    /// - input - the sequence to parse.
    /// - is_partial - `true` to return all complete `T`s, or `false` to treat
    ///   partial input as an error.
    fn parse_all(&self, input: impl IntoIterator<Item=Self::Input>, is_partial: bool)
    -> Result<Box<[Self::Output]>, Option<Self::Error>> {
        let mut stream = IteratorStream::from(input);
        let mut ret = Vec::new();
        while !stream.is_empty() {
            match self.parse_one(&mut stream) {
                Ok(None) => {},
                Ok(Some(item)) => { ret.push(item); }
                Err(message) => {
                    if message.is_none() && is_partial { break; }
                    return Err(message);
                },
            }
        }
        Ok(ret.into())
    }
}

// ----------------------------------------------------------------------------

/// An implementation of `Stream<T>` that transparently tracks [`Location`]s.
#[derive(Debug)]
struct LocStream<S> {
    /// The wrapped [`Stream<Loc<T>>`].
    inner: S,

    /// The [`Location`] of the item that can be `unread()`, if any.
    ///
    /// This is cleared by `union_loc()`.
    last_loc: Option<Location>,

    /// The union of the [`Location`]s of all items that were `read()` and that
    /// can no longer by `unread()`.
    ///
    /// This is cleared by `union_loc()`.
    union_loc: Option<Location>,
}

impl<S> LocStream<S> {
    fn new(inner: S) -> Self { Self { inner, last_loc: None, union_loc: None } }

    /// Incorporate `last_loc` into `union_loc`. This vacates `last_loc`.
    fn shift(&mut self) {
        let Some(mut loc) = self.last_loc.take() else { return; };
        if let Some(old_loc) = self.union_loc.take() {
            assert!(old_loc.end <= loc.start);
            loc.start = old_loc.start;
        }
        self.union_loc = Some(loc);
    }

    /// Returns the [`Location`] of the last [`Self::Item`] that was `read()`,
    /// if any.
    ///
    /// The `Location` is consumed; you cannot next `unread()`.
    pub fn last_loc(&mut self) -> Option<Location> {
        self.last_loc.take()
    }

    /// Returns the union of the [`Location`]s of all [`Self::Item`]s `read()`
    /// since the last call to `union_loc()`, omitting those consumed by
    /// `unread()` or by `last_loc()`.
    ///
    /// The `Location`s are consumed; you cannot next `unread()`.
    pub fn union_loc(&mut self) -> Option<Location> {
        self.shift();
        self.union_loc.take()
    }
}

impl<T, S: Stream<Item=Loc<T>>> Stream for LocStream<S> {
    type Item = T;

    fn read(&mut self) -> Option<Self::Item> {
        self.shift();
        self.inner.read().map(|Loc(item, loc)| {
            self.last_loc = Some(loc);
            item
        })
    }

    fn unread(&mut self, item: Self::Item) {
        let loc = self.last_loc.take().expect("`unread() before `read()`");
        self.inner.unread(Loc(item, loc));
    }
}

// ----------------------------------------------------------------------------

/// Parse a [`Stream`] of [`Loc<P::Input>`] to make a [`Loc<P::Output>`].
#[derive(Debug, Clone)]
pub struct LocParser<P: Parse>(pub P);

impl<P: Parse> Parse for LocParser<P> {
    type Input = Loc<P::Input>;
    type Output = Loc<P::Output>;
    type Error = Loc<P::Error>;

    fn parse_one(&self, input: &mut impl Stream<Item=Self::Input>)
    -> Result<Option<Self::Output>, Option<Self::Error>> {
        let mut loc_input = LocStream::new(input);
        match self.0.parse_one(&mut loc_input) {
            Ok(maybe_output) => Ok(maybe_output.map(|output| {
                let loc = loc_input.union_loc().expect("`parse_one()` did not read any input");
                Loc(output, loc)
            })),
            Err(maybe_error) => Err(maybe_error.map(|error| {
                let loc = loc_input.last_loc().expect("`parse_one()` did not read any input");
                Loc(error, loc)
            })),
        }
    }
}
