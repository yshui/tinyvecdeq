use core::ops::{Range, RangeBounds};
use std::collections::VecDeque;

use crate::array::Array;

#[repr(C)]
pub struct ArrayVecDeq<A> {
    array: A,
    head:  usize,
    len:   usize,
}

impl<A> Clone for ArrayVecDeq<A>
where
    A: Clone + Array,
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
        self.overwrite_with(source.iter())
    }
}
impl<A> Copy for ArrayVecDeq<A>
where
    A: Clone + Copy + Array,
    A::Item: Clone,
{
}
impl<A: Array> Default for ArrayVecDeq<A> {
    fn default() -> Self {
        Self {
            array: Array::default(),
            head:  0,
            len:   0,
        }
    }
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

struct IterWithLen<I> {
    iter: I,
    len:  usize,
}

impl<I> Iterator for IterWithLen<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let elem = self.iter.next()?;
        self.len -= 1;
        Some(elem)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<I> ExactSizeIterator for IterWithLen<I>
where
    I: Iterator,
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<A> ArrayVecDeq<A>
where
    A: Array,
{
    /// Drains all elements to a VecDeque, but reserves additional space
    /// ```
    /// # use tinyvecdeq::arrayvecdeq::ArrayVecDeq;
    /// let mut av = ArrayVecDeq::new([0i32; 7]);
    /// av.extend(1..=3);
    /// let v = av.drain_to_vec_and_reserve(10);
    /// assert_eq!(v, &[1, 2, 3]);
    /// assert_eq!(v.capacity(), 13);
    /// ```
    pub fn drain_to_vec_and_reserve(&mut self, n: usize) -> VecDeque<A::Item> {
        let cap = n + self.len();
        let mut v = VecDeque::with_capacity(cap);
        let iter = self.iter_mut().map(std::mem::take);
        v.extend(iter);
        self.len = 0;
        v
    }

    #[inline]
    pub(crate) fn overwrite_with<'other>(
        &mut self,
        source: impl ExactSizeIterator<Item = &'other A::Item>,
    ) where
        A::Item: Clone + 'other,
    {
        let source_len = source.len();
        let iter = self.array.as_slice_mut().iter_mut().zip(source);
        for (dst, src) in iter {
            dst.clone_from(src);
        }
        if let Some(to_drop) = self
            .array
            .as_slice_mut()
            .get_mut(self.head.max(source_len)..)
        {
            to_drop.iter_mut().for_each(|x| *x = A::Item::default());
        }

        if self.len > self.capacity() - self.head {
            let end = self.len - (self.capacity() - self.head);
            if let Some(to_drop) = self.array.as_slice_mut().get_mut(source_len..end) {
                to_drop.iter_mut().for_each(|x| *x = A::Item::default());
            }
        }
        self.head = 0;
        self.len = source_len;
    }

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

    /// Makes a new, empty `ArrayVecDeq`.
    #[inline]
    pub fn new(a: A) -> Self {
        Self {
            array: a,
            head:  0,
            len:   0,
        }
    }

    /// Clone each element of the slice into this `ArrayVecDeq`.
    ///
    /// #Panics
    ///
    /// If the `ArrayVecDeq` would overflow, this will panic.
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[A::Item])
    where
        A::Item: Clone,
    {
        let x = self.try_extend_from_slice(other);
        assert!(
            x.is_none(),
            "ArrayVecDeq::extend_from_slice: not enough capacity"
        );
    }

    #[inline]
    pub fn try_extend_from_slice<'other>(
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

    /// Returns an iterator over the elements of the `ArrayVecDeq`.
    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = &mut A::Item> + '_ {
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        let chain = if first.len() >= self.len {
            first[..self.len].iter_mut().chain([].iter_mut())
        } else {
            let second_len = self.len - first.len();
            first.iter_mut().chain(second[..second_len].iter_mut())
        };
        IterWithLen {
            iter: chain,
            len:  self.len,
        }
    }

    /// Returns an iterator over the elements of the `ArrayVecDeq`.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &A::Item> + '_ {
        let (second, first) = self.array.as_slice().split_at(self.head);
        let chain = if first.len() >= self.len {
            first[..self.len].iter().chain([].iter())
        } else {
            let second_len = self.len - first.len();
            first.iter().chain(second[..second_len].iter())
        };
        IterWithLen {
            iter: chain,
            len:  self.len,
        }
    }

    /// Move all values from `other` to the end of this `ArrayVecDeq`
    ///
    /// #Panics
    ///
    /// If the `ArrayVecDeq` would overflow, this will panic.
    #[inline]
    pub fn append(&mut self, other: &'_ mut Self) {
        let x = self.try_append(other);
        assert!(x.is_none(), "ArrayVecDeq::append: not enough capacity");
    }

    #[inline]
    pub fn try_append<'other>(&mut self, other: &'other mut Self) -> Option<&'other mut Self> {
        let new_len = self.len + other.len;
        if new_len > self.capacity() {
            return Some(other)
        }
        for item in other.drain(..) {
            self.push_back(item);
        }
        None
    }

    /// Length of the `ArrayVecDeq`.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// If the `ArrayVecDeq` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Provides a reference to the front element, or `None` if the
    /// `ArrayVecDeq` is empty.
    #[inline]
    pub fn front(&self) -> Option<&A::Item> {
        if !self.is_empty() {
            self.array.as_slice().get(self.head)
        } else {
            None
        }
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `ArrayVecDeq` is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut A::Item> {
        if !self.is_empty() {
            self.array.as_slice_mut().get_mut(self.head)
        } else {
            None
        }
    }

    /// Provides a reference to the back element, or `None` if the
    /// `ArrayVecDeq` is empty.
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
    /// `ArrayVecDeq` is empty.
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
    /// `ArrayVecDeq`.
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

    /// Returns the capacity of the `ArrayVecDeq`.
    pub fn capacity(&self) -> usize {
        A::CAPACITY
    }

    /// Remove all elements from the `ArrayVecDeq`.
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
        struct Drain<'a, A: Array> {
            inner: &'a mut ArrayVecDeq<A>,
            curr:  usize,
            start: usize,
            end:   usize,
        }

        impl<A: Array> Iterator for Drain<'_, A> {
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
        impl<A: Array> Drop for Drain<'_, A> {
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
    /// Index 0 is the front of the `ArrayVecDeq`.
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
    /// Index 0 is the front of the `ArrayVecDeq`.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut A::Item> {
        if index < self.len {
            let index = wrap_add(self.head, index, A::CAPACITY);
            self.array.as_slice_mut().get_mut(index)
        } else {
            None
        }
    }

    /// Remove the last element from the `ArrayVecDeq` and return it, or
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

    /// Remove the first element from the `ArrayVecDeq` and return it, or
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
    /// front of the `ArrayVecDeq`.
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

    /// Appends an element to the back of the `ArrayVecDeq`.
    ///
    /// Returns `None` if the `ArrayVecDeq` is full.
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

    /// Prepends an element to the front of the `ArrayVecDeq`.
    ///
    /// Returns `None` if the `ArrayVecDeq` is full.
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

    /// Appends an element to the back of the `ArrayVecDeq`.
    ///
    /// # Panics
    ///
    /// Panics if the `ArrayVecDeq` is full.
    #[inline]
    pub fn push_back(&mut self, item: A::Item) {
        let x = self.try_push_back(item);
        assert!(x.is_none(), "ArrayVecDeq capacity overflow");
    }

    /// Prepends an element to the front of the `ArrayVecDeq`.
    ///
    /// # Panics
    ///
    /// Panics if the `ArrayVecDeq` is full.
    #[inline]
    pub fn push_front(&mut self, item: A::Item) {
        let x = self.try_push_front(item);
        assert!(x.is_none(), "ArrayVecDeq capacity overflow");
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
        assert!(x.is_none(), "ArrayVecDeq capacity overflow");
    }

    /// Inserts an element at index within the deque, shifting all elements with
    /// indices greater than or equal to index towards the back. Returns the
    /// item if the deque is full.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if index is greater than deque’s length
    #[inline]
    pub fn try_insert(&mut self, index: usize, item: A::Item) -> Option<A::Item> {
        assert!(index <= self.len, "ArrayVecDeq index out of bounds");
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
    pub fn remove(&mut self, index: usize) -> Option<A::Item> {
        if index >= self.len {
            return None
        }
        for i in (index..self.len - 1).rev() {
            self.swap(i, self.len - 1);
        }
        Some(self.pop_back().unwrap())
    }
}

impl<A: Array> Extend<A::Item> for ArrayVecDeq<A> {
    #[inline]
    fn extend<T: IntoIterator<Item = A::Item>>(&mut self, iter: T) {
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<A: Array> PartialEq for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<A: Array> Eq for ArrayVecDeq<A> where A::Item: Eq {}

impl<A: Array> PartialEq<&[A::Item]> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&[A::Item]) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}
impl<A: Array> PartialEq<&mut [A::Item]> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&mut [A::Item]) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<A: Array, const N: usize> PartialEq<&[A::Item; N]> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&[A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: Array, const N: usize> PartialEq<&mut [A::Item; N]> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&mut [A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: Array, const N: usize> PartialEq<[A::Item; N]> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[A::Item; N]) -> bool {
        self.len == N && self.iter().eq(other.iter())
    }
}

impl<A: Array> PartialEq<Vec<A::Item>> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Vec<A::Item>) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<A: Array> PartialEq<VecDeque<A::Item>> for ArrayVecDeq<A>
where
    A::Item: PartialEq,
{
    #[inline]
    fn eq(&self, other: &VecDeque<A::Item>) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<A: Array> std::fmt::Debug for ArrayVecDeq<A>
where
    A::Item: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
/// Check if unused elements are initialized to the default value.
pub(crate) fn check_spare<A>(v: &ArrayVecDeq<A>)
where
    A: Array,
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

#[cfg(test)]
mod test {
    // Tests taken from the VecDeque tests
    use super::*;

    crate::gen_tests_internal!(ArrayVecDeq);
    crate::gen_tests!(ArrayVecDeq);
}
