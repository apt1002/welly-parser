/// An [`Iterator`] with an `undo()` method.
// TODO: Move to a `util` module.
pub struct UndoIterator<I: Iterator> {
    /// The underlying [`Iterator`].
    input: I,

    /// A stack of items to be `pop()`ped before reading `input.next()`.
    stack: Vec<I::Item>,
}

impl<I: Iterator> UndoIterator<I> {
    pub fn new(input: I) -> Self { Self {input, stack: Vec::new()} }

    /// Give an item back to this [`Iterator`], such that it will be returned
    /// by the next call to [`self.next()`].
    pub fn undo(&mut self, item: I::Item) { self.stack.push(item); }
}

impl<I: Iterator> Iterator for UndoIterator<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().or_else(|| self.input.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (low, high) = self.input.size_hint();
        let n = self.stack.len();
        (
            low.checked_add(n).unwrap_or(usize::MAX),
            high.and_then(|high| high.checked_add(n)),
        )
    }
}
