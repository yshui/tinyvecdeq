use std::ops::{Range, RangeBounds};

#[repr(C)]
pub struct ArrayVecDeque<A> {
    array: A,
    head:  usize,
    len:   usize,
}

impl<A> Clone for ArrayVecDeque<A>
where
    A: Clone + tinyvec::Array,
    A::Item: Clone,
{
    fn clone(&self) -> Self {
        Self {
            array: self.array.clone(),
            head:  self.head,
            len:   self.len,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        let iter = self.array.as_slice_mut().iter_mut().zip(source.iter());
        for (dst, src) in iter {
            dst.clone_from(src);
        }
        if let Some(to_drop) = self
            .array
            .as_slice_mut()
            .get_mut(self.head.max(source.len)..)
        {
            to_drop.iter_mut().for_each(|x| *x = A::Item::default());
        }

        if self.len > self.capacity() - self.head {
            let end = self.len - (self.capacity() - self.head);
            if let Some(to_drop) = self.array.as_slice_mut().get_mut(source.len..end) {
                to_drop.iter_mut().for_each(|x| *x = A::Item::default());
            }
        }
        self.head = 0;
        self.len = source.len;
    }
}
impl<A> Copy for ArrayVecDeque<A>
where
    A: Clone + Copy + tinyvec::Array,
    A::Item: Clone,
{
}

/// Overflow-safe addition that wraps around the capacity.
#[inline]
fn wrap_add(head: usize, offset: usize, capacity: usize) -> usize {
    debug_assert!(
        (head == 0 && offset == 0 && capacity == 0) || (offset < capacity && head < capacity),
        "{head} + {offset} (mod {capacity})",
    );

    if capacity < usize::MAX / 2 {
        // Using % makes everything way faster for some reason, but it won't handle
        // overflow properly. So if you use an array bigger than 8 EiB, you will
        // have a performance hit. ¯\_(ツ)_/¯
        (offset + head) % capacity
    } else if offset >= capacity - head {
        offset - (capacity - head)
    } else {
        head + offset
    }
}

#[inline]
fn discrete_range<R: RangeBounds<usize>>(range: R, len: usize) -> (usize, usize) {
    use std::ops::Bound;
    let start = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&n) => n + 1,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => len,
    };
    (start, end)
}

impl<A> ArrayVecDeque<A>
where
    A: tinyvec::Array,
{
    /// Obtain the shared slice of the parts of array that aren't used.
    #[inline]
    pub fn grab_spare_slices(&self) -> (&[A::Item], &[A::Item]) {
        let (second, first) = self.array.as_slice().split_at(self.head);
        if first.len() > self.len {
            (&first[self.len..], second)
        } else {
            (&[], &second[self.len - first.len()..])
        }
    }

    /// Makes a new, empty `ArrayVecDeque`.
    #[inline]
    pub fn new(a: A) -> Self {
        Self {
            array: a,
            head:  0,
            len:   0,
        }
    }

    /// Clone each element of the slice into this `ArrayVecDeque`.
    ///
    /// #Panics
    ///
    /// If the `ArrayVecDeque` would overflow, this will panic.
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[A::Item])
    where
        A::Item: Clone,
    {
        let x = self.try_extend_from_slice(other);
        assert!(
            x.is_none(),
            "ArrayVecDeque::extend_from_slice: not enough capacity"
        );
    }

    #[inline]
    fn try_extend_from_slice<'other>(
        &mut self,
        other: &'other [A::Item],
    ) -> Option<&'other [A::Item]>
    where
        A::Item: Clone,
    {
        let new_len = self.len + other.len();
        if new_len > self.capacity() {
            return Some(other)
        }
        let capacity = self.capacity();
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        if first.len() >= self.len {
            let first_len = first.len();
            let first_cap = (capacity - self.len).min(other.len());
            let second_cap = (capacity - first.len()).min(other.len() - first_cap);
            first[first_len..].clone_from_slice(&other[..first_cap]);
            if second_cap > 0 {
                second[..second_cap].clone_from_slice(&other[first_cap..]);
            }
        } else {
            let second_len = self.len + other.len() - first.len();
            second[self.len - first.len()..second_len].clone_from_slice(other);
        }
        None
    }

    /// Returns an iterator over the elements of the `ArrayVecDeque`.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut A::Item> + '_ {
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        if first.len() >= self.len {
            first[..self.len].iter_mut().chain([].iter_mut())
        } else {
            let second_len = self.len - first.len();
            first.iter_mut().chain(second[..second_len].iter_mut())
        }
    }

    /// Returns an iterator over the elements of the `ArrayVecDeque`.
    pub fn iter(&self) -> impl Iterator<Item = &A::Item> + '_ {
        let (second, first) = self.array.as_slice().split_at(self.head);
        if first.len() >= self.len {
            first[..self.len].iter().chain([].iter())
        } else {
            let second_len = self.len - first.len();
            first.iter().chain(second[..second_len].iter())
        }
    }

    /// Move all values from `other` to the end of this `ArrayVecDeque`
    ///
    /// #Panics
    ///
    /// If the `ArrayVecDeque` would overflow, this will panic.
    #[inline]
    pub fn append(&mut self, other: &'_ mut Self) {
        let x = self.try_append(other);
        assert!(x.is_none(), "ArrayVecDeque::append: not enough capacity");
    }

    #[inline]
    fn try_append<'other>(&mut self, other: &'other mut Self) -> Option<&'other mut Self> {
        let new_len = self.len + other.len;
        if new_len > self.capacity() {
            return Some(other)
        }
        for item in other.drain(..) {
            self.push_back(item);
        }
        None
    }

    /// Length of the `ArrayVecDeque`.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// If the `ArrayVecDeque` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Provides a reference to the front element, or `None` if the
    /// `ArrayVecDeque` is empty.
    #[inline]
    pub fn front(&self) -> Option<&A::Item> {
        if !self.is_empty() {
            self.array.as_slice().get(self.head)
        } else {
            None
        }
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `ArrayVecDeque` is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut A::Item> {
        if !self.is_empty() {
            self.array.as_slice_mut().get_mut(self.head)
        } else {
            None
        }
    }

    /// Provides a reference to the back element, or `None` if the
    /// `ArrayVecDeque` is empty.
    #[inline]
    pub fn back(&self) -> Option<&A::Item> {
        if !self.is_empty() {
            let index = wrap_add(self.head, self.len - 1, A::CAPACITY);
            self.array.as_slice().get(index)
        } else {
            None
        }
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// `ArrayVecDeque` is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut A::Item> {
        if !self.is_empty() {
            let index = wrap_add(self.head, self.len - 1, A::CAPACITY);
            self.array.as_slice_mut().get_mut(index)
        } else {
            None
        }
    }

    /// Returns a pair of slices which contains the contents of the
    /// `ArrayVecDeque`.
    ///
    /// If [`make_contiguous`] was previously called, all elements will be in
    /// the first slice, and the second slice will be empty.
    #[inline]
    pub fn as_slices(&self) -> (&[A::Item], &[A::Item]) {
        let (second, first) = self.array.as_slice().split_at(self.head);
        if first.len() >= self.len {
            (first[..self.len].as_ref(), &[])
        } else {
            let second_len = self.len - first.len();
            (first, second[..second_len].as_ref())
        }
    }

    /// Same as [`as_slices`], but returns mutable slices.
    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [A::Item], &mut [A::Item]) {
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        if first.len() >= self.len {
            (first[..self.len].as_mut(), &mut [])
        } else {
            let second_len = self.len - first.len();
            (first, second[..second_len].as_mut())
        }
    }

    /// Returns the capacity of the `ArrayVecDeque`.
    pub fn capacity(&self) -> usize {
        A::CAPACITY
    }

    /// Remove all elements from the `ArrayVecDeque`.
    pub fn clear(&mut self) {
        for item in self.iter_mut() {
            *item = A::Item::default();
        }
        self.len = 0;
        self.head = 0;
    }

    /// Removes the specified range from the deque in bulk, returning all
    /// removed elements as an iterator. If the iterator is dropped before being
    /// fully consumed, it drops the remaining removed elements.
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> impl Iterator<Item = A::Item> + '_ {
        struct Drain<'a, A: tinyvec::Array> {
            inner: &'a mut ArrayVecDeque<A>,
            curr:  usize,
            start: usize,
            end:   usize,
        }

        impl<A: tinyvec::Array> Iterator for Drain<'_, A> {
            type Item = A::Item;

            fn next(&mut self) -> Option<Self::Item> {
                if self.curr == self.end {
                    return None
                }

                let elem = self.inner.get_mut(self.curr).unwrap();
                self.curr += 1;
                Some(std::mem::take(elem))
            }
        }
        impl<A: tinyvec::Array> Drop for Drain<'_, A> {
            fn drop(&mut self) {
                let removed = self.end - self.start;
                if self.start == 0 {
                    while self.curr != self.end {
                        std::mem::take(self.inner.get_mut(self.curr).unwrap());
                        self.curr += 1;
                    }
                    if self.end < self.inner.len {
                        self.inner.head = wrap_add(self.inner.head, self.end, A::CAPACITY);
                    } else {
                        self.inner.head = 0;
                    }
                } else {
                    for i in self.start..self.inner.len - removed {
                        *self.inner.get_mut(i).unwrap() =
                            std::mem::take(self.inner.get_mut(i + removed).unwrap());
                    }
                }
                self.inner.len -= removed;
            }
        }
        let (start, end) = discrete_range(range, self.len);
        Drain::<A> {
            inner: self,
            curr: start,
            start,
            end,
        }
    }

    /// Provides a reference to the element at the given index.
    ///
    /// Index 0 is the front of the `ArrayVecDeque`.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&A::Item> {
        if index < self.len {
            let index = wrap_add(self.head, index, A::CAPACITY);
            self.array.as_slice().get(index)
        } else {
            None
        }
    }

    /// Provides a mutable reference to the element at the given index.
    ///
    /// Index 0 is the front of the `ArrayVecDeque`.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut A::Item> {
        if index < self.len {
            let index = wrap_add(self.head, index, A::CAPACITY);
            self.array.as_slice_mut().get_mut(index)
        } else {
            None
        }
    }

    /// Remove the last element from the `ArrayVecDeque` and return it, or
    /// `None` if it is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<A::Item> {
        if self.len == 0 {
            None
        } else {
            let item = std::mem::take(self.get_mut(self.len - 1).unwrap());
            self.len -= 1;
            Some(item)
        }
    }

    /// Remove the first element from the `ArrayVecDeque` and return it, or
    /// `None` if it is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<A::Item> {
        if self.len == 0 {
            None
        } else {
            let item = std::mem::take(self.get_mut(0).unwrap());
            self.head = wrap_add(self.head, 1, A::CAPACITY);
            self.len -= 1;
            Some(item)
        }
    }

    /// Swap elements at indices `a` and `b`.
    ///
    /// `a` and `b` must be equal. Element at index 0 is the front of the
    /// front of the `ArrayVecDeque`.
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    #[inline]
    pub fn swap(&mut self, a: usize, b: usize) {
        assert!(a < self.len);
        assert!(b < self.len);
        if a != b {
            let a = wrap_add(self.head, a, A::CAPACITY);
            let b = wrap_add(self.head, b, A::CAPACITY);
            self.array.as_slice_mut().swap(a, b);
        }
    }

    /// Removes an element at the given index in the deque and returns it,
    /// replacing it with the last element.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn swap_remove_back(&mut self, index: usize) -> Option<A::Item> {
        if index < self.len {
            self.swap(index, self.len - 1);
            self.pop_back()
        } else {
            None
        }
    }

    /// Removes an element at the given index in the deque and returns it,
    /// replacing it with the first element.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn swap_remove_front(&mut self, index: usize) -> Option<A::Item> {
        if index < self.len {
            self.swap(index, 0);
            self.pop_front()
        } else {
            None
        }
    }

    /// Appends an element to the back of the `ArrayVecDeque`.
    ///
    /// Returns `None` if the `ArrayVecDeque` is full.
    #[inline]
    pub fn try_push_back(&mut self, item: A::Item) -> Option<A::Item> {
        if self.len == A::CAPACITY {
            Some(item)
        } else {
            self.len += 1;
            *self.back_mut().unwrap() = item;
            None
        }
    }

    /// Prepends an element to the front of the `ArrayVecDeque`.
    ///
    /// Returns `None` if the `ArrayVecDeque` is full.
    #[inline]
    pub fn try_push_front(&mut self, item: A::Item) -> Option<A::Item> {
        if self.len == A::CAPACITY {
            Some(item)
        } else {
            self.head = wrap_add(self.head, A::CAPACITY - 1, A::CAPACITY);
            self.len += 1;
            self.array.as_slice_mut()[self.head] = item;
            None
        }
    }

    /// Appends an element to the back of the `ArrayVecDeque`.
    ///
    /// # Panics
    ///
    /// Panics if the `ArrayVecDeque` is full.
    #[inline]
    pub fn push_back(&mut self, item: A::Item) {
        let x = self.try_push_back(item);
        assert!(x.is_none(), "ArrayVecDeque capacity overflow");
    }

    /// Prepends an element to the front of the `ArrayVecDeque`.
    ///
    /// # Panics
    ///
    /// Panics if the `ArrayVecDeque` is full.
    #[inline]
    pub fn push_front(&mut self, item: A::Item) {
        let x = self.try_push_front(item);
        assert!(x.is_none(), "ArrayVecDeque capacity overflow");
    }

    /// Rearranges the internal storage of this deque so it is one contiguous
    /// slice, which is then returned.
    ///
    /// This method does not change the order of the inserted elements. As it
    /// returns a mutable slice, this can be used to sort a deque.
    ///
    /// Once the internal storage is contiguous, the as_slices and as_mut_slices
    /// methods will return the entire contents of the deque in a single slice.
    ///
    /// # Complexity
    ///
    /// Always O(capacity).
    #[inline]
    pub fn make_contiguous(&mut self) -> &mut [A::Item] {
        if self.capacity() - self.head >= self.len {
            return &mut self.array.as_slice_mut()[self.head..self.head + self.len]
        }
        self.array.as_slice_mut().rotate_left(self.head);
        self.head = 0;
        &mut self.array.as_slice_mut()[..self.len]
    }

    #[inline]
    fn slice_ranges<R: RangeBounds<usize>>(
        &self,
        range: R,
    ) -> Option<(Range<usize>, Range<usize>)> {
        let (start, end) = discrete_range(range, self.len);
        let first_len = self.capacity() - self.head;
        if start < first_len {
            if end <= first_len {
                Some((start..end, 0..0))
            } else if end <= self.len {
                Some((start..first_len, 0..(end - first_len)))
            } else {
                None
            }
        } else if end <= self.len {
            Some((0..0, start - first_len..end - first_len))
        } else {
            None
        }
    }

    /// Returns an iterator over the elements of the deque in the given range.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    #[inline]
    pub fn range<R>(&self, range: R) -> impl Iterator<Item = &A::Item> + '_
    where
        R: RangeBounds<usize>,
    {
        let (second, first) = self.array.as_slice().split_at(self.head);
        let (range_first, range_second) = self.slice_ranges(range).unwrap();
        first
            .get(range_first)
            .unwrap()
            .iter()
            .chain(second.get(range_second).unwrap().iter())
    }

    /// Returns an iterator over the elements of the deque in the given range.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    #[inline]
    pub fn range_mut<R>(&mut self, range: R) -> impl Iterator<Item = &mut A::Item> + '_
    where
        R: RangeBounds<usize> + std::fmt::Debug,
    {
        let (range_first, range_second) = self.slice_ranges(range).unwrap();
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        first
            .get_mut(range_first)
            .unwrap()
            .iter_mut()
            .chain(second.get_mut(range_second).unwrap().iter_mut())
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns
    /// `false`.
    #[inline]
    pub fn retain_mut<F: FnMut(&mut A::Item) -> bool>(&mut self, mut predicate: F) {
        // If a chunk of the front is removed, we just need to move head without moving
        // any elements.
        while self.len > 0 && !predicate(self.get_mut(0).unwrap()) {
            self.pop_front();
        }

        // We already ran predicate on the first element, so start at 1.
        let mut write = 1;
        let mut removed = 0;
        for read in 1..self.len {
            if predicate(self.get_mut(read).unwrap()) {
                if read != write {
                    *self.get_mut(write).unwrap() = std::mem::take(self.get_mut(read).unwrap());
                }
                write += 1;
            } else {
                removed += 1;
            }
        }
        self.len -= removed;
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns
    /// `false`.
    #[inline]
    pub fn retain<F: FnMut(&A::Item) -> bool>(&mut self, mut predicate: F) {
        self.retain_mut(|e| predicate(e))
    }

    /// Shortens the deque, keeping the first len elements and dropping the
    /// rest.
    ///
    /// If len is greater than the deque’s current length, this has no
    /// effect.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len < self.len {
            for item in self.range_mut(len..) {
                std::mem::take(item);
            }
            self.len = len;
        }
    }

    /// Inserts an element at index within the deque, shifting all elements with
    /// indices greater than or equal to index towards the back.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if index is greater than deque’s length, or if the deque is full
    #[inline]
    pub fn insert(&mut self, index: usize, item: A::Item) {
        let x = self.try_insert(index, item);
        assert!(x.is_none(), "ArrayVecDeque capacity overflow");
    }

    /// Inserts an element at index within the deque, shifting all elements with
    /// indices greater than or equal to index towards the back. Returns the item
    /// if the deque is full.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if index is greater than deque’s length
    #[inline]
    pub fn try_insert(&mut self, index: usize, item: A::Item) -> Option<A::Item> {
        assert!(index <= self.len, "ArrayVecDeque index out of bounds");
        if let Some(item) = self.try_push_back(item) {
            return Some(item)
        }

        // Rotate item into place
        for i in index..self.len - 1 {
            self.swap(i, self.len - 1);
        }
        None
    }

    /// Remove an element at index within the deque, shifting all elements with
    /// indices greater than index towards the front.
    #[inline]
    pub fn remove(&mut self, index: usize) -> A::Item {
        assert!(index < self.len, "ArrayVecDeque index out of bounds");
        for i in (index..self.len - 1).rev() {
            self.swap(i, self.len - 1);
        }
        self.pop_back().unwrap()
    }
}

impl<A: tinyvec::Array> Extend<A::Item> for ArrayVecDeque<A> {
    #[inline]
    fn extend<T: IntoIterator<Item = A::Item>>(&mut self, iter: T) {
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<A: tinyvec::Array> PartialEq for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array> Eq for ArrayVecDeque<A> where A::Item: Eq {}

impl<A: tinyvec::Array> PartialEq<&[A::Item]> for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&[A::Item]) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array, const N: usize> PartialEq<&[A::Item; N]> for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&[A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array, const N: usize> PartialEq<&mut [A::Item; N]> for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&mut [A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array, const N: usize> PartialEq<[A::Item; N]> for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array> PartialEq<Vec<A::Item>> for ArrayVecDeque<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Vec<A::Item>) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<A: tinyvec::Array> std::fmt::Debug for ArrayVecDeque<A>
where
    A::Item: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod test {
    // Tests taken from the VecDeque tests
    use super::*;

    /// Check if unused elements are initialized to the default value.
    fn check_spare<A>(v: &ArrayVecDeque<A>)
    where
        A: tinyvec::Array,
        A::Item: Default + PartialEq + std::fmt::Debug,
    {
        let (spare1, spare2) = v.grab_spare_slices();
        assert!(
            spare1.iter().all(|x| *x == Default::default()),
            "{:?}",
            spare1
        );
        assert!(
            spare2.iter().all(|x| *x == Default::default()),
            "{:?}",
            spare2
        );
    }
    #[test]
    fn test_swap_front_back_remove() {
        fn test(back: bool) {
            // This test checks that every single combination of tail position and length is
            // tested. Capacity 15 should be large enough to cover every case.
            let mut tester = ArrayVecDeque::new([0; 15]);
            let usable_cap = tester.capacity();
            let final_len = usable_cap / 2;

            for len in 0..final_len {
                let mut expected = ArrayVecDeque::new([0; 15]);
                if back {
                    expected.extend(0..len)
                } else {
                    expected.extend((0..len).rev())
                };
                for head_pos in 0..usable_cap {
                    tester.head = head_pos;
                    tester.len = 0;
                    if back {
                        for i in 0..len * 2 {
                            tester.push_front(i);
                        }
                        for i in 0..len {
                            assert_eq!(tester.swap_remove_back(i), Some(len * 2 - 1 - i));
                        }
                    } else {
                        for i in 0..len * 2 {
                            tester.push_back(i);
                        }
                        for i in 0..len {
                            let idx = tester.len() - 1 - i;
                            assert_eq!(tester.swap_remove_front(idx), Some(len * 2 - 1 - i));
                        }
                    }
                    assert!(tester.head <= tester.capacity());
                    assert!(tester.len <= tester.capacity());
                    assert_eq!(tester, expected);
                }
            }
        }
        test(true);
        test(false);
    }

    #[test]
    fn test_insert() {
        // This test checks that every single combination of tail position, length, and
        // insertion position is tested. Capacity 15 should be large enough to cover
        // every case.

        let mut tester = ArrayVecDeque::new([0; 15]);
        // can't guarantee we got 15, so have to get what we got.
        // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
        // this test isn't covering what it wants to
        let cap = tester.capacity();

        // len is the length *after* insertion
        let minlen = if cfg!(miri) { cap - 1 } else { 1 }; // Miri is too slow
        for len in minlen..cap {
            // 0, 1, 2, .., len - 1
            let mut expected = ArrayVecDeque::new([0; 15]);
            expected.extend((0..).take(len));
            for head_pos in 0..cap {
                for to_insert in 0..len {
                    tester.head = head_pos;
                    tester.len = 0;
                    for i in 0..len {
                        if i != to_insert {
                            tester.push_back(i);
                        }
                    }
                    tester.insert(to_insert, to_insert);
                    assert_eq!(tester, expected);
                }
            }
        }
    }
    #[test]
    fn test_get() {
        let mut tester = ArrayVecDeque::new([0; 5]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);

        assert_eq!(tester.len(), 3);

        assert_eq!(tester.get(1), Some(&2));
        assert_eq!(tester.get(2), Some(&3));
        assert_eq!(tester.get(0), Some(&1));
        assert_eq!(tester.get(3), None);

        tester.remove(0);

        assert_eq!(tester.len(), 2);
        assert_eq!(tester.get(0), Some(&2));
        assert_eq!(tester.get(1), Some(&3));
        assert_eq!(tester.get(2), None);
    }
    #[test]
    fn test_get_mut() {
        let mut tester = ArrayVecDeque::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);

        assert_eq!(tester.len(), 3);

        if let Some(elem) = tester.get_mut(0) {
            assert_eq!(*elem, 1);
            *elem = 10;
        }

        if let Some(elem) = tester.get_mut(2) {
            assert_eq!(*elem, 3);
            *elem = 30;
        }

        assert_eq!(tester.get(0), Some(&10));
        assert_eq!(tester.get(2), Some(&30));
        assert_eq!(tester.get_mut(3), None);

        tester.remove(2);

        assert_eq!(tester.len(), 2);
        assert_eq!(tester.get(0), Some(&10));
        assert_eq!(tester.get(1), Some(&2));
        assert_eq!(tester.get(2), None);
    }

    #[test]
    fn test_swap() {
        let mut tester = ArrayVecDeque::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);

        assert_eq!(tester, [1, 2, 3]);

        tester.swap(0, 0);
        assert_eq!(tester, [1, 2, 3]);
        tester.swap(0, 1);
        assert_eq!(tester, [2, 1, 3]);
        tester.swap(2, 1);
        assert_eq!(tester, [2, 3, 1]);
        tester.swap(1, 2);
        assert_eq!(tester, [2, 1, 3]);
        tester.swap(0, 2);
        assert_eq!(tester, [3, 1, 2]);
        tester.swap(2, 2);
        assert_eq!(tester, [3, 1, 2]);
    }

    #[test]
    #[should_panic = "assertion failed: b < self.len"]
    fn test_swap_panic() {
        let mut tester = ArrayVecDeque::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);
        tester.swap(2, 3);
    }
    #[test]
    fn make_contiguous_big_head() {
        let mut tester = ArrayVecDeque::new([0; 15]);

        for i in 0..3 {
            tester.push_back(i);
        }

        for i in 3..10 {
            tester.push_front(i);
        }

        // 012......9876543
        assert_eq!(tester.capacity(), 15);
        assert_eq!(
            (&[9, 8, 7, 6, 5, 4, 3] as &[_], &[0, 1, 2] as &[_]),
            tester.as_slices()
        );

        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (&[9, 8, 7, 6, 5, 4, 3, 0, 1, 2] as &[_], &[] as &[_]),
            tester.as_slices()
        );
        check_spare(&tester);
    }

    #[test]
    fn make_contiguous_big_tail() {
        let mut tester = ArrayVecDeque::new([0; 15]);

        for i in 0..8 {
            tester.push_back(i);
        }

        for i in 8..10 {
            tester.push_front(i);
        }

        // 01234567......98
        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (&[9, 8, 0, 1, 2, 3, 4, 5, 6, 7] as &[_], &[] as &[_]),
            tester.as_slices()
        );
        check_spare(&tester);
    }

    #[test]
    fn make_contiguous_small_free() {
        let mut tester = ArrayVecDeque::new([0 as char; 16]);

        for i in b'A'..b'I' {
            tester.push_back(i as char);
        }

        for i in b'I'..b'N' {
            tester.push_front(i as char);
        }

        assert_eq!(tester, [
            'M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'
        ]);

        // ABCDEFGH...MLKJI
        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (
                &['M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'] as &[_],
                &[] as &[_]
            ),
            tester.as_slices()
        );
        check_spare(&tester);

        tester.clear();
        for i in b'I'..b'N' {
            tester.push_back(i as char);
        }

        for i in b'A'..b'I' {
            tester.push_front(i as char);
        }

        // IJKLM...HGFEDCBA
        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (
                &['H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'I', 'J', 'K', 'L', 'M'] as &[_],
                &[] as &[_]
            ),
            tester.as_slices()
        );
        check_spare(&tester);
    }

    #[test]
    fn make_contiguous_head_to_end() {
        let mut tester = ArrayVecDeque::new([0 as char; 16]);

        for i in b'A'..b'L' {
            tester.push_back(i as char);
        }

        for i in b'L'..b'Q' {
            tester.push_front(i as char);
        }

        assert_eq!(tester, [
            'P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K'
        ]);

        // ABCDEFGHIJKPONML
        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (
                &['P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K']
                    as &[_],
                &[] as &[_]
            ),
            tester.as_slices()
        );
        check_spare(&tester);

        tester.clear();
        for i in b'L'..b'Q' {
            tester.push_back(i as char);
        }

        for i in b'A'..b'L' {
            tester.push_front(i as char);
        }

        // LMNOPKJIHGFEDCBA
        tester.make_contiguous();
        assert_eq!(tester.head, 0);
        assert_eq!(
            (
                &['K', 'J', 'I', 'H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'L', 'M', 'N', 'O', 'P']
                    as &[_],
                &[] as &[_]
            ),
            tester.as_slices()
        );
        check_spare(&tester);
    }

    #[test]
    fn make_contiguous_head_to_end_2() {
        // Another test case for #79808, taken from #80293.

        let mut dq = ArrayVecDeque::new([0; 16]);
        dq.extend(0..6);
        dq.pop_front();
        dq.pop_front();
        dq.push_back(6);
        dq.push_back(7);
        dq.push_back(8);
        dq.make_contiguous();
        let collected: Vec<_> = dq.iter().copied().collect();
        assert_eq!(dq.as_slices(), (&collected[..], &[] as &[_]));
        check_spare(&dq);
    }

    #[test]
    fn test_remove() {
        // This test checks that every single combination of tail position, length, and
        // removal position is tested. Capacity 15 should be large enough to cover every
        // case.

        // can't guarantee we got 15, so have to get what we got.
        // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
        // this test isn't covering what it wants to
        const CAP: usize = 15;

        // len is the length *after* removal
        let minlen = if cfg!(miri) { CAP - 2 } else { 0 }; // Miri is too slow
        for len in minlen..CAP - 1 {
            // 0, 1, 2, .., len - 1
            let mut expected = ArrayVecDeque::new([0; 15]);
            expected.extend((0..).take(len));
            for head_pos in 0..CAP {
                for to_remove in 0..=len {
                    let mut tester = ArrayVecDeque::new([0; CAP]);
                    tester.head = head_pos;
                    for i in 0..len {
                        if i == to_remove {
                            tester.push_back(1234);
                        }
                        tester.push_back(i);
                    }
                    if to_remove == len {
                        tester.push_back(1234);
                    }
                    tester.remove(to_remove);
                    assert!(tester.head <= tester.capacity());
                    assert!(tester.len <= tester.capacity());
                    assert_eq!(tester, expected);
                    check_spare(&tester);
                }
            }
        }
    }
    #[test]
    fn test_range() {
        const CAP: usize = 7;
        let minlen = if cfg!(miri) { CAP - 1 } else { 0 }; // Miri is too slow
        for len in minlen..=CAP {
            for head in 0..CAP {
                for start in 0..=len {
                    for end in start..=len {
                        let mut tester = ArrayVecDeque::new([0; CAP]);
                        tester.head = head;
                        for i in 0..len {
                            tester.push_back(i);
                        }

                        // Check that we iterate over the correct values
                        let range: Vec<_> = tester.range(start..end).copied().collect();
                        let expected: Vec<_> = (start..end).collect();
                        assert_eq!(range, expected);
                    }
                }
            }
        }
    }

    #[test]
    fn test_range_mut() {
        const CAP: usize = 7;

        for len in 0..=CAP {
            for head in 0..CAP {
                for start in 0..=len {
                    for end in start..=len {
                        let mut tester = ArrayVecDeque::new([0; CAP]);
                        tester.head = head;
                        for i in 0..len {
                            tester.push_back(i);
                        }

                        let head_was = tester.head;
                        let len_was = tester.len;

                        // Check that we iterate over the correct values
                        let range: Vec<_> = tester.range_mut(start..end).map(|v| *v).collect();
                        let expected: Vec<_> = (start..end).collect();
                        assert_eq!(range, expected);

                        // We shouldn't have changed the capacity or made the
                        // head or tail out of bounds
                        assert_eq!(tester.head, head_was);
                        assert_eq!(tester.len, len_was);
                    }
                }
            }
        }
    }

    #[test]
    fn test_drain() {
        const CAP: usize = 7;

        for len in 0..=CAP {
            for head in 0..CAP {
                for drain_start in 0..=len {
                    for drain_end in drain_start..=len {
                        let mut tester = ArrayVecDeque::new([0; CAP]);
                        tester.head = head;
                        tester.len = 0;
                        for i in 0..len {
                            tester.push_back(i);
                        }

                        // Check that we drain the correct values
                        let drained: Vec<_> = tester.drain(drain_start..drain_end).collect();
                        let drained_expected: Vec<_> = (drain_start..drain_end).collect();
                        assert_eq!(drained, drained_expected);

                        // We shouldn't have changed the capacity or made the
                        // head or tail out of bounds
                        assert!(tester.head <= tester.capacity());
                        assert!(tester.len <= tester.capacity());

                        // We should see the correct values in the VecDeque
                        let expected: Vec<_> = (0..drain_start).chain(drain_end..len).collect();
                        assert_eq!(tester, expected, "{drain_start:?} {drain_end:?}");
                        check_spare(&tester);
                    }
                }
            }
        }
    }
    #[test]
    fn test_clone_from() {
        let m = vec![1; 8];
        let n = vec![2; 12];
        let limit = if cfg!(miri) { 4 } else { 8 }; // Miri is too slow
        for pfv in 0..limit {
            for pfu in 0..limit {
                for longer in 0..2 {
                    let (vr, ur) = if longer == 0 { (&m, &n) } else { (&n, &m) };
                    let mut v = ArrayVecDeque::new([0; 20]);
                    v.extend(vr.iter().copied());
                    for _ in 0..pfv {
                        v.push_front(1);
                    }
                    let mut u = ArrayVecDeque::new([0; 20]);
                    u.extend(ur.iter().copied());
                    for _ in 0..pfu {
                        u.push_front(2);
                    }
                    v.clone_from(&u);
                    assert_eq!(&v, &u);
                    check_spare(&v);
                    check_spare(&u);
                }
            }
        }
    }
}
