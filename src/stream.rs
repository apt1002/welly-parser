use super::loc::{self, Location, Loc};

/// A stream of items.
pub trait Stream {
    /// The return type of `read()`.
    type Item;

    /// Read the next item, or raise [`loc::Error::InsufficientInput`].
    fn read(&mut self) -> Result<Self::Item, loc::Error>;

    /// Unread `item`. The next call to `read()` will return `item`.
    ///
    /// # Panics
    ///
    /// If you `unread()` more than one item.
    fn unread(&mut self, item: Self::Item);

    /// Returns `true` if there are no more [`Self::Item`]s to `read()`.
    fn is_empty(&mut self) -> bool {
        if let Ok(item) = self.read() {
            self.unread(item);
            false
        } else {
            true
        }
    }
}

impl<'a, S: Stream> Stream for &'a mut S {
    type Item = S::Item;
    fn read(&mut self) -> Result<Self::Item, loc::Error> { S::read(*self) }
    fn unread(&mut self, item: Self::Item) { S::unread(*self, item) }
    fn is_empty(&mut self) -> bool { S::is_empty(*self) }
}

// ----------------------------------------------------------------------------

/// A [`Stream`] implemented in terms of an [`Iterator`].
#[derive(Debug)]
pub struct IteratorStream<I: Iterator> {
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

    fn read(&mut self) -> Result<Self::Item, loc::Error> {
        self.item.take().or_else(|| self.iter.next()).ok_or(loc::Error::InsufficientInput)
    }

    fn unread(&mut self, item: Self::Item) {
        assert!(self.item.is_none());
        self.item = Some(item);
    }
}

// ----------------------------------------------------------------------------

/// An [`Iterator`] yielding `Loc<char>`.
pub struct CharIterator<'a> {
    remaining: std::str::Chars<'a>,
    length: usize,
}

impl<'a> CharIterator<'a> {
    pub fn new(source_code: &'a str, start_pos: usize) -> Self {
        Self {remaining: source_code[start_pos..].chars(), length: source_code.len() }
    }

    pub fn pos(&self) -> usize { self.length - self.remaining.as_str().len() }
}

impl<'a> Iterator for CharIterator<'a> {
    type Item = Loc<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.pos();
        let Some(c) = self.remaining.next() else { return None; };
        let end = self.pos();
        Some(Loc(c, Location {start, end}))
    }
}
