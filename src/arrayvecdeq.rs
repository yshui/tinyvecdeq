use core::ops::RangeBounds;
use std::{collections::VecDeque, mem::MaybeUninit};

use crate::array::Array;

/// A fixed size double-ended queue backed by an array.
#[repr(C)]
pub struct ArrayVecDeq<A: Array> {
    array: MaybeUninit<A>,
    head:  usize,
    len:   usize,
}

impl<A> Clone for ArrayVecDeq<A>
where
    A: Clone + Array,
    A::Item: Clone,
{
    fn clone(&self) -> Self {
        let mut other = Self::default();
        let (head, tail) = self.as_slices();
        other.extend_from_slice(head);
        other.extend_from_slice(tail);
        other
    }
}

impl<A: Array> Drop for ArrayVecDeq<A> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Array> Default for ArrayVecDeq<A> {
    fn default() -> Self {
        Self {
            array: MaybeUninit::uninit(),
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

/// Normalize a range against an array of length `len`. Return start and end
/// point of the normalized range [start, end).
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
    if end < start {
        (0, 0)
    } else {
        (start, end)
    }
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
    /// let mut av = ArrayVecDeq::<[_; 7]>::new();
    /// av.extend(1..=3);
    /// let v = av.drain_to_vec_and_reserve(10);
    /// assert_eq!(v, &[1, 2, 3]);
    /// assert_eq!(v.capacity(), 13);
    /// ```
    pub fn drain_to_vec_and_reserve(&mut self, n: usize) -> VecDeque<A::Item> {
        let cap = n + self.len();
        let mut v = VecDeque::with_capacity(cap);
        let (head, tail) = self.as_mut_slices_uninit();
        let iter = head.iter_mut().chain(tail).map(|it| {
            let it = std::mem::replace(it, MaybeUninit::uninit());
            // SAFETY: Invariant of `as_mut_slices_uninit`.
            unsafe { it.assume_init() }
        });
        v.extend(iter);
        self.len = 0;
        v
    }

    /// Obtain the parts of the underlying array that aren't used.
    ///
    /// Slices are returned in the order they are arranged in memory.
    ///
    /// - [b | head | a] -> return (b, a) (b may be empty)
    /// - [ tail | b | head ] -> return (b, &[])
    ///
    /// Invariant: the total length of the two slices adds up to
    /// `self.capacity() - self.len()`.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn grab_spare_slices(&self) -> (&[MaybeUninit<A::Item>], &[MaybeUninit<A::Item>]) {
        // SAFETY: Invariant: self.head is within bounds.
        let (second, first) =
            unsafe { Array::transpose_uninit(&self.array).split_at_unchecked(self.head) };

        // |second| + |first| = CAPACITY,
        // self.len - |first| <= CAPACITY - |first| = |second|
        // therefore tail_len <= |second|
        let head_len = self.len.min(first.len());
        let tail_len = self.len.saturating_sub(first.len());

        // SAFETY: tail_len <= second.len(), head_len <= first.len()
        unsafe {
            (
                second.get_unchecked(tail_len..),
                first.get_unchecked(head_len..),
            )
        }
    }

    /// See [`Self::grab_spare_slices`].
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn grab_spare_slices_mut(
        &mut self,
    ) -> (&mut [MaybeUninit<A::Item>], &mut [MaybeUninit<A::Item>]) {
        // SAFETY: Invariant: self.head is within bounds.
        let (second, first) = unsafe {
            Array::transpose_uninit_mut(&mut self.array).split_at_mut_unchecked(self.head)
        };

        // |second| + |first| = CAPACITY,
        // self.len - |first| <= CAPACITY - |first| = |second|
        // therefore tail_len <= |second|
        let head_len = self.len.min(first.len());
        let tail_len = self.len.saturating_sub(first.len());

        // SAFETY: tail_len <= second.len(), head_len <= first.len()
        unsafe {
            (
                second.get_unchecked_mut(tail_len..),
                first.get_unchecked_mut(head_len..),
            )
        }
    }

    /// Makes a new, empty `ArrayVecDeq`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Copy each element of the slice into this `ArrayVecDeq`, extending its
    /// length.
    ///
    /// #Panics
    ///
    /// If the `ArrayVecDeq` would overflow, this will panic.
    #[inline]
    pub fn extend_from_slice_copying(&mut self, other: &[A::Item])
    where
        A::Item: Copy,
    {
        let x = self.try_extend_from_slice_copying(other);
        assert!(x, "ArrayVecDeq::extend_from_slice: not enough capacity");
    }

    #[inline]
    pub fn try_extend_from_slice_copying(&mut self, mut other: &[A::Item]) -> bool
    where
        A::Item: Copy,
    {
        let new_len = self.len + other.len();
        if new_len > A::CAPACITY {
            return false
        }

        // layout: [ tail | a | head | b ]
        let (a, b) = self.grab_spare_slices_mut();
        let to_copy = b.len().min(other.len());
        // SAFETY: to_copy <= after_tail.len() && to_copy <= other.len()
        unsafe {
            (b.as_mut_ptr() as *mut A::Item).copy_from_nonoverlapping(other.as_ptr(), to_copy);
        };

        other = &other[to_copy..];

        // other' = other[to_copy..]
        // to_copy + other'.len() = other.len()
        //
        // to_copy + other'.len() <= capacity - self.len
        //                        [ Invariant of grab_spare_slices_mut ]
        //                        <= a.len() + b.len().
        //
        // since either to_copy == other.len() <1>, or to_copy == b.len() <2>.
        //
        // for <1> : other'.len() == 0 <= a.len()
        // for <2> : other'.len() <= a.len() + b.len() - b.len()
        //           other'.len() <= a.len() [cancel]

        // SAFETY: other'.len() <= a.len().
        unsafe {
            (a.as_mut_ptr() as *mut A::Item).copy_from_nonoverlapping(other.as_ptr(), other.len());
        }
        self.len = new_len;
        true
    }

    #[inline]
    pub fn try_extend_from_slice(&mut self, other: &[A::Item]) -> bool
    where
        A::Item: Clone,
    {
        let new_len = self.len + other.len();
        if new_len > A::CAPACITY {
            return false
        }
        // layout: [ tail | a | head | b ]
        let (a, b) = self.grab_spare_slices_mut();
        for (dst, src) in b.iter_mut().chain(a).zip(other) {
            dst.write(src.clone());
        }
        self.len = new_len;
        true
    }

    /// Clone each element of the slice into this `ArrayVecDeq`, extending its
    /// length.
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
        assert!(x, "ArrayVecDeq::extend_from_slice: not enough capacity");
    }

    /// Returns an iterator over the elements of the `ArrayVecDeq`.
    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = &mut A::Item> + '_ {
        let len = self.len;
        let (head, tail) = self.as_mut_slices();
        IterWithLen {
            iter: head.iter_mut().chain(tail),
            len,
        }
    }

    /// Returns an iterator over the elements of the `ArrayVecDeq`.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &A::Item> + '_ {
        let (head, tail) = self.as_slices();
        IterWithLen {
            iter: head.iter().chain(tail),
            len:  self.len,
        }
    }

    /// Move all values from `other` to the end of this `ArrayVecDeq`
    ///
    /// # Panics
    ///
    /// If the `ArrayVecDeq` would overflow, this will panic.
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        let x = self.try_append(other);
        assert!(x, "ArrayVecDeq::append: not enough capacity");
    }

    #[inline]
    pub fn try_append(&mut self, other: &'_ mut Self) -> bool {
        let new_len = self.len + other.len;
        if new_len > self.capacity() {
            return false
        }
        for item in other.drain(..) {
            self.push_back(item);
        }
        true
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
        self.get(0)
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `ArrayVecDeq` is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut A::Item> {
        self.get_mut(0)
    }

    /// Provides a reference to the back element, or `None` if the
    /// `ArrayVecDeq` is empty.
    #[inline]
    pub fn back(&self) -> Option<&A::Item> {
        if self.len > 0 {
            self.get(self.len - 1)
        } else {
            None
        }
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// `ArrayVecDeq` is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut A::Item> {
        if self.len > 0 {
            self.get_mut(self.len - 1)
        } else {
            None
        }
    }

    /// Same as [`Self::as_slices`], but return them as `MaybeUninit` slices.
    ///
    /// Invariant: both returned slices contain initialized elements.
    #[inline]
    #[allow(clippy::type_complexity)]
    fn as_slices_uninit(&self) -> (&[MaybeUninit<A::Item>], &[MaybeUninit<A::Item>]) {
        // SAFETY: Invariant: self.head is within bounds.
        let (second, first) =
            unsafe { Array::transpose_uninit(&self.array).split_at_unchecked(self.head) };
        let first_len = first.len(); // avoid borrowing `first`.

        // trim the uninitialized parts off
        // SAFETY:
        // 1) self.len - first_len <= first_len + second_len - first_len = second_len.
        // 2) min(first_len, self.len) <= first_len.
        unsafe {
            (
                first.get_unchecked(..first_len.min(self.len)),
                second.get_unchecked(..self.len.saturating_sub(first_len)),
            )
        }

        // SAFETY: self.len elements are initialized. so both return slices are
        // initialized.
    }

    /// Same as [`Self::as_mut_slices`], but return them as `MaybeUninit`
    /// slices.
    ///
    /// Invariant: both returned slices contain initialized elements.
    #[inline]
    #[allow(clippy::type_complexity)]
    fn as_mut_slices_uninit(
        &mut self,
    ) -> (&mut [MaybeUninit<A::Item>], &mut [MaybeUninit<A::Item>]) {
        // SAFETY: Invariant: self.head is within bounds.
        let (second, first) = unsafe {
            Array::transpose_uninit_mut(&mut self.array).split_at_mut_unchecked(self.head)
        };
        let first_len = first.len(); // avoid borrowing `first`.

        // trim the uninitialized parts off
        // SAFETY:
        // 1) self.len - first_len <= first_len + second_len - first_len = second_len.
        // 2) min(first_len, self.len) <= first_len.
        unsafe {
            (
                first.get_unchecked_mut(..first_len.min(self.len)),
                second.get_unchecked_mut(..self.len.saturating_sub(first_len)),
            )
        }

        // SAFETY: self.len elements are initialized. so both return slices are
        // initialized.
    }

    /// Returns a pair of slices which contains the contents of the
    /// `ArrayVecDeq`. The slices are returned in logical order, i.e.
    /// elements with smaller indices are returned first. (As opposed to
    /// memory order, as is the case for [`grab_spare_slices`]).
    ///
    /// If [`make_contiguous`] was previously called, all elements will be in
    /// the first slice, and the second slice will be empty.
    #[inline]
    pub fn as_slices(&self) -> (&[A::Item], &[A::Item]) {
        let (head, tail) = self.as_slices_uninit();

        // SAFETY: Invariant of `as_slices_uninit`.
        unsafe { (head.assume_init_ref(), tail.assume_init_ref()) }
    }

    /// Same as [`as_slices`], but returns mutable slices.
    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [A::Item], &mut [A::Item]) {
        let (head, tail) = self.as_mut_slices_uninit();
        // SAFETY: Invariant of `as_mut_slices_uninit`.
        unsafe { (head.assume_init_mut(), tail.assume_init_mut()) }
    }

    /// Returns the capacity of the `ArrayVecDeq`.
    pub fn capacity(&self) -> usize {
        A::CAPACITY
    }

    /// Remove all elements from the `ArrayVecDeq`.
    #[inline]
    pub fn clear(&mut self) {
        let (head, tail) = self.as_mut_slices_uninit();
        if A::NEEDS_DROP {
            for item in head.iter_mut().chain(tail) {
                // SAFETY: Invariant of `as_mut_slices_uninit`.
                unsafe { item.assume_init_drop() };
            }
        }
        self.len = 0;
    }

    /// Removes the specified range from the deque in bulk, returning all
    /// removed elements as an iterator. If the iterator is dropped before being
    /// fully consumed, it drops the remaining removed elements.
    ///
    /// # Panics
    ///
    /// If `range` is out of bounds.
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

                let elem = self.inner.get_mut_uninit(self.curr).unwrap();
                self.curr += 1;
                // SAFETY: element is initialized. and after this function returns,
                // it will be treated by `ArrayVecDeq` as logically uninitialized,
                // so it's Ok to use `read`.
                Some(unsafe { elem.as_mut_ptr().read() })
            }
        }
        impl<A: Array> Drop for Drain<'_, A> {
            fn drop(&mut self) {
                let removed = self.end - self.start;
                if removed == 0 {
                    return;
                }

                let arr = Array::transpose_uninit_mut(&mut self.inner.array);
                if self.start == 0 {
                    // Drop from the start, only need to move `head`, no need to move elements.

                    if A::NEEDS_DROP {
                        // Drop the remaining elements.
                        while self.curr != self.end {
                            let curr_idx = wrap_add(self.inner.head, self.curr, A::CAPACITY);
                            // SAFETY: start and end indices are validated in `drain` to be within
                            // self.len, so they are within bounds. self.curr are after the last
                            // element we dropped, so it is initialized.
                            unsafe { arr.get_unchecked_mut(curr_idx).assume_init_drop() };
                            self.curr += 1;
                        }
                    }
                    if self.end < self.inner.len {
                        self.inner.head = wrap_add(self.inner.head, self.end, A::CAPACITY);
                    } else {
                        self.inner.head = 0;
                    }
                } else {
                    for i in self.start..self.inner.len - removed {
                        let write_idx = wrap_add(self.inner.head, i, A::CAPACITY);
                        let read_idx = wrap_add(write_idx, removed, A::CAPACITY);
                        // SAFETY: wrap_add returns indices that are within bounds.
                        let [write, read] =
                            unsafe { arr.get_disjoint_unchecked_mut([write_idx, read_idx]) };
                        if A::NEEDS_DROP && i >= self.curr {
                            // This element hasn't been dropped yet.
                            // SAFETY: Only elements within [start, curr) have been dropped,
                            // The rest are still initialized.
                            unsafe { write.assume_init_drop() };
                        }
                        // Now it has been dropped, we can overwrite it directly.
                        // SAFETY: Both read and write are valid, read_idx != write_idx. And
                        // after this copy, the read element becomes logically uninitialized.
                        unsafe {
                            write
                                .as_mut_ptr()
                                .copy_from_nonoverlapping(read.as_ptr(), 1)
                        };
                    }

                    if A::NEEDS_DROP {
                        // Drop leftovers between [curr, end). Notice everything up to
                        // (self.inner.len - removed) has been processed, and dropped if needed.
                        for i in (self.inner.len - removed).max(self.curr)..self.end {
                            // SAFETY: wrap_add only returns indices that are within bounds.
                            let to_drop = unsafe {
                                arr.get_unchecked_mut(wrap_add(self.inner.head, i, A::CAPACITY))
                            };
                            // SAFETY: `i` is an index after self.curr, so it hasn't been returned
                            // by the Drain iterator, therefore must be
                            // dropped.
                            unsafe {
                                to_drop.assume_init_drop();
                            }
                        }
                    }
                }
                self.inner.len -= removed;
            }
        }
        let (start, end) = discrete_range(range, self.len);
        if end > start {
            assert!(
                start < self.len,
                "array start index out of bound, len {}, index {start}",
                self.len
            );
            assert!(
                end <= self.len,
                "array end index out of bound, len {}, index {end}",
                self.len
            );

            Drain::<A> {
                inner: self,
                curr: start,
                start,
                end,
            }
        } else {
            Drain::<A> {
                inner: self,
                curr:  0,
                start: 0,
                end:   0,
            }
        }
    }

    /// Same as [`Self::get`], but return as a `MaybeUninit`.
    ///
    /// Invariant: the returned element is initialized.
    #[inline]
    fn get_uninit(&self, index: usize) -> Option<&MaybeUninit<A::Item>> {
        if index < self.len {
            let index = wrap_add(self.head, index, A::CAPACITY);
            // SAFETY: We just checked that `index` is in bounds of initialized elements.
            Some(unsafe { Array::transpose_uninit(&self.array).get_unchecked(index) })
        } else {
            None
        }
    }

    /// Provides a reference to the element at the given index.
    ///
    /// Index 0 is the front of the `ArrayVecDeq`.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&A::Item> {
        let e = self.get_uninit(index)?;
        // SAFETY: Invariant of `get_uninit`.
        Some(unsafe { e.assume_init_ref() })
    }

    /// Same as [`Self::get_mut`], but return as a `MaybeUninit`.
    ///
    /// Invariant: the returned element is initialized.
    #[inline]
    fn get_mut_uninit(&mut self, index: usize) -> Option<&mut MaybeUninit<A::Item>> {
        if index < self.len {
            let index = wrap_add(self.head, index, A::CAPACITY);
            // SAFETY: We just checked that `index` is in bounds of initialized elements.
            Some(unsafe { Array::transpose_uninit_mut(&mut self.array).get_unchecked_mut(index) })
        } else {
            None
        }
    }

    /// Provides a mutable reference to the element at the given index.
    ///
    /// Index 0 is the front of the `ArrayVecDeq`.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut A::Item> {
        let e = self.get_mut_uninit(index)?;
        // SAFETY: Invariant of `get_mut_uninit`.
        Some(unsafe { e.assume_init_mut() })
    }

    /// Remove the last element from the `ArrayVecDeq` and return it, or
    /// `None` if it is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<A::Item> {
        let back = self.get_mut_uninit(self.len - 1)?;
        let back = std::mem::replace(back, MaybeUninit::uninit());
        // Invariant: self.len is always the number of initialized elements
        self.len -= 1;
        // SAFETY: Invariant of `get_mut_uninit`.
        Some(unsafe { back.assume_init() })
    }

    /// Remove the first element from the `ArrayVecDeq` and return it, or
    /// `None` if it is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<A::Item> {
        let front = self.get_mut_uninit(0)?;
        let front = std::mem::replace(front, MaybeUninit::uninit());
        // Invariant: self.len is always the number of initialized elements
        self.len -= 1;
        // Invariant: self.head always points to an initialized element if self.len is
        // not 0.
        self.head = wrap_add(self.head, 1, A::CAPACITY);
        // SAFETY: Invariant of `get_mut_uninit`.
        Some(unsafe { front.assume_init() })
    }

    /// Swap elements at indices `a` and `b`.
    ///
    /// `a` and `b` must be equal. Element at index 0 is the front of the
    /// front of the `ArrayVecDeq`.
    ///
    /// # Panics
    ///
    /// Panics if either `a` or `b` is out of bounds.
    #[inline]
    pub fn swap(&mut self, a: usize, b: usize) {
        assert!(a < self.len);
        assert!(b < self.len);
        if a != b {
            let a = wrap_add(self.head, a, A::CAPACITY);
            let b = wrap_add(self.head, b, A::CAPACITY);
            let arr = Array::transpose_uninit_mut(&mut self.array);
            arr.swap(a, b);
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
            // Invariant: self.head points to initialized element, and self.len is
            // the number of initialized elements.
            let index = wrap_add(self.head, self.len, A::CAPACITY);
            let arr = Array::transpose_uninit_mut(&mut self.array);
            // SAFETY: index is within bounds.
            unsafe { arr.get_unchecked_mut(index) }.write(item);

            self.len += 1;
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
            // Invariant: self.head points to initialized element, and self.len is
            // the number of initialized elements.
            self.head = wrap_add(self.head, A::CAPACITY - 1, A::CAPACITY);
            self.len += 1;

            let arr = Array::transpose_uninit_mut(&mut self.array);
            // SAFETY: self.head is within bounds after the mutations above.
            unsafe { arr.get_unchecked_mut(self.head) }.write(item);
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
        let arr = Array::transpose_uninit_mut(&mut self.array);
        if A::CAPACITY - self.head >= self.len {
            // SAFETY: self.head is within bounds.
            let (_, ret) = unsafe { arr.split_at_mut_unchecked(self.head) };
            // SAFETY: ret.len() = A::CAPACITY - self.head >= self.len.
            // And self.len elements are initialized.
            return unsafe { ret.get_unchecked_mut(..self.len).assume_init_mut() }
        }
        arr.rotate_left(self.head);
        self.head = 0;

        // SAFETY: after rotation, first self.len elements are initialized.
        // And self.len is within bounds.
        unsafe { arr.get_unchecked_mut(..self.len).assume_init_mut() }
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
        // Invariant: start <= A::CAPACITY, end <= A::CAPACITY.
        let (start, end) = discrete_range(range, self.len);
        let (head, tail) = self.as_slices();
        let head_len = head.len();
        // SAFETY: both start end are clamped to head_len;
        let head = unsafe { head.get_unchecked(start.min(head_len)..end.min(head_len)) };
        let tail = &tail[start.saturating_sub(head_len)..end.saturating_sub(head_len)];
        head.iter().chain(tail)
    }

    /// Same as [`Self::range_mut`], but return as `MaybeUninit`. The returned
    /// elements are all initialized.
    #[inline]
    fn range_uninit_mut<R>(
        &mut self,
        range: R,
    ) -> impl Iterator<Item = &mut MaybeUninit<A::Item>> + '_
    where
        R: RangeBounds<usize> + std::fmt::Debug,
    {
        // Invariant: start <= A::CAPACITY, end <= A::CAPACITY.
        let (start, end) = discrete_range(range, self.len);
        let (head, tail) = self.as_mut_slices_uninit();
        let head_len = head.len();
        // SAFETY: both start end are clamped to head_len;
        let head = unsafe { head.get_unchecked_mut(start.min(head_len)..end.min(head_len)) };
        let tail = &mut tail[start.saturating_sub(head_len)..end.saturating_sub(head_len)];
        head.iter_mut().chain(tail)
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
        // Invariant: start <= A::CAPACITY, end <= A::CAPACITY.
        let (start, end) = discrete_range(range, self.len);
        let (head, tail) = self.as_mut_slices();
        let head_len = head.len();
        // SAFETY: both start end are clamped to head_len;
        let head = unsafe { head.get_unchecked_mut(start.min(head_len)..end.min(head_len)) };
        let tail = &mut tail[start.saturating_sub(head_len)..end.saturating_sub(head_len)];
        head.iter_mut().chain(tail)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns
    /// `false`.
    #[inline]
    pub fn retain_mut<F: FnMut(&mut A::Item) -> bool>(&mut self, mut predicate: F) {
        // If a chunk of the front is removed, we just need to move head without moving
        // any elements.
        loop {
            let Some(front) = self.get_mut_uninit(0) else {
                return;
            };
            // SAFETY: Invariant of `get_mut_uninit`.
            if !predicate(unsafe { front.assume_init_mut() }) {
                self.pop_front();
            } else {
                break;
            }
        }

        // Now try to find the first element we need to drop
        let mut spare = 0;
        loop {
            let Some(elem) = self.get_mut_uninit(spare) else {
                return;
            };
            // SAFETY: Invariant of `get_mut_uninit`.
            if predicate(unsafe { elem.assume_init_mut() }) {
                spare += 1;
            } else {
                if A::NEEDS_DROP {
                    // SAFETY: Invariant of `get_mut_uninit`.
                    unsafe { elem.assume_init_drop() };
                }
                break;
            }
        }

        let mut removed = 1;

        // Loop invariants:
        // 1) spare < read.
        // 2) elements in [spare, read) are uninitialized.
        //
        // Base case:
        // 1) spare < read because spare < spare + 1.
        // 2) we just dropped the element at index 0.
        let arr = Array::transpose_uninit_mut(&mut self.array);
        for read in spare + 1..self.len {
            let spare_idx = wrap_add(self.head, spare, A::CAPACITY);
            let read_idx = wrap_add(self.head, read, A::CAPACITY);
            // SAFETY: wrap_add always returns an index within bounds. spare != read because
            // loop invariant.
            let [read_elem, spare_elem] =
                unsafe { arr.get_disjoint_unchecked_mut([read_idx, spare_idx]) };
            // SAFETY: read < self.len, so its initialized.
            if predicate(unsafe { read_elem.assume_init_mut() }) {
                // SAFETY: Loop invariant, read != spare. And both spare and read are valid
                // elements.
                unsafe {
                    spare_elem
                        .as_mut_ptr()
                        .copy_from_nonoverlapping(read_elem.as_mut_ptr(), 1)
                };
                spare += 1;
            } else {
                if A::NEEDS_DROP {
                    // SAFETY: read < self.len, so its initialized.
                    unsafe { read_elem.assume_init_drop() };
                }
                removed += 1;
            }
            // Induction step:
            // 1) `read` always increment by 1 per loop, `spare` only increment
            //    some of the times. So (read' = read + 1) > (spare' = spare +
            //    inc), where inc <= 1.
            // 2) If `predicate` returns true, elements are copied from read to
            //    spare, After copying, the element at spare become initialized,
            //    and the element at read become uninitialized, we increment
            //    spare and read, so all elements within [spare, read) are still
            //    uninitialized. If `predicate` returned false, we
            //    `assume_init_drop` the element at read, making it
            //    uninitialized, the element at spare is unchanged. And we
            //    increment read so all elements in [spare, read) are
            //    uninitialized.
        }

        // Invariant: read == self.len at loop exit. Therefore &arr[spare..] are
        // uninitialized. We just need to decrement len, no need to drop these
        // elements.
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
            for item in self.range_uninit_mut(len..) {
                // SAFETY: Invariant of `range_uninit_mut`.
                unsafe { item.assume_init_drop() };
            }
            self.len = len;
        }
    }

    /// Shortens the deque, keeping the last `len` elements and dropping the
    /// rest.
    ///
    /// If len is greater than the deque’s current length, this has no
    /// effect.
    #[inline]
    pub fn truncate_front(&mut self, len: usize) {
        if len < self.len {
            for item in self.range_uninit_mut(..self.len - len) {
                // SAFETY: Invariant of `range_uninit_mut`.
                unsafe { item.assume_init_drop() };
            }
            self.head += self.len - len;
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
mod test {
    // Tests taken from the VecDeque tests
    use super::*;

    crate::gen_tests_internal!(ArrayVecDeq);
    crate::gen_tests!(ArrayVecDeq);
}
