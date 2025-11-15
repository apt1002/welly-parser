/// A stream of `T`.
// TODO: each with a [`Location`].
pub trait Stream<T> {
    /// Returns `true` if there are no more `T`s to `read()`.
    fn is_empty(&mut self) -> bool;

    /// Read the next item, if any.
    fn read(&mut self) -> Option<T>;

    /// Unread `item`. The next call to `read()` will return `item`.
    ///
    /// # Panics
    ///
    /// If you `unread()` more than one item.
    fn unread(&mut self, item: T);
}

// ----------------------------------------------------------------------------

/// A [`Stream`] implemented in terms of an [`Iterator`].
struct IteratorStream<I: Iterator> {
    /// The underlying [`Iterator`].
    iter: I,

    /// Optionally, a value to return before fetching one from `iter`.
    item: Option<I::Item>,
}

impl<I: IntoIterator> From<I> for IteratorStream<I::IntoIter> {
    fn from(value: I) -> Self { Self {iter: value.into_iter(), item: None} }
}

impl<I: Iterator> Stream<<I as Iterator>::Item> for IteratorStream<I> {
    fn is_empty(&mut self) -> bool {
        self.item = self.read();
        self.item.is_none()
    }

    fn read(&mut self) -> Option<I::Item> {
        if let Some(item) = self.item.take() { return Some(item); }
        let Some(item) = self.iter.next() else { return None; };
        Some(item)
    }

    fn unread(&mut self, item: I::Item) {
        assert!(self.item.is_none());
        self.item = Some(item);
    }
}

// ----------------------------------------------------------------------------

/// Parse a stream of [`Self::Input`] to make a `T`.
pub trait Parse<T> {
    /// The item type of the stream parsed by `Self`.
    type Input;

    /// Attempt to parse one `T`.
    ///
    /// Returns:
    /// - Ok(None) - Some useless [`Self::Input`]s were discarded.
    /// - Ok(Some(item)) - Some [`Self::Input`]s were combined into `item`.
    /// - Err("") - there were not enough [`Self::Input`]s to parse a `T`.
    /// - Err(message) - Some invalid [`Self::Input`]s were discarded.
    fn parse_one(&self, input: &mut impl Stream<Self::Input>, ) -> Result<Option<T>, &'static str>;

    /// Parse a sequence of [`Self::Input`] into a sequence of `T`, or return
    /// the first error.
    ///
    /// - input - the sequence to parse.
    /// - is_partial - `true` to return all complete `T`s, or `false` to treat
    ///   partial input as an error.
    fn parse_all(&self, input: impl IntoIterator<Item=Self::Input>, is_partial: bool)
    -> Result<Box<[T]>, &'static str> {
        let mut stream = IteratorStream::from(input);
        let mut ret = Vec::new();
        while !stream.is_empty() {
            match self.parse_one(&mut stream) {
                Ok(None) => {},
                Ok(Some(item)) => { ret.push(item); }
                Err(message) => {
                    if message.len() == 0 && is_partial { break; }
                    return Err(message);
                },
            }
        }
        Ok(ret.into())
    }
}
