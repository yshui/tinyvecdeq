use alloc::collections::VecDeque;
use std::ops::RangeBounds;

use either::Either;

use crate::{array::Array, arrayvecdeq::ArrayVecDeq};

#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub enum TinyVecDeq<A: Array> {
    Inline(ArrayVecDeq<A>),
    Heap(VecDeque<A::Item>),
}

impl<A: Array> Default for TinyVecDeq<A>
{
    #[inline]
    fn default() -> Self {
        TinyVecDeq::Inline(Default::default())
    }
}

impl<A> Clone for TinyVecDeq<A>
where
    A: Array + Clone,
    A::Item: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        match self {
            TinyVecDeq::Inline(v) => TinyVecDeq::Inline(v.clone()),
            TinyVecDeq::Heap(v) => TinyVecDeq::Heap(v.clone()),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        if source.len() <= A::CAPACITY {
            match self {
                TinyVecDeq::Inline(v) => v.overwrite_with(source.iter()),
                TinyVecDeq::Heap(_) => {
                    *self = TinyVecDeq::Inline(Default::default());
                },
            }
        }
    }
}

macro_rules! impl_mirrored {
    {
    type Mirror = $tinyname:ident;
    $(
        $(#[$attr:meta])*
        $v:vis fn $fname:ident ($seif:ident : $seifty:ty $(,$argname:ident : $argtype:ty)*) $(-> $ret:ty)? ;
    )*
    } => {
        $(
        $(#[$attr])*
        #[inline(always)]
        $v fn $fname($seif : $seifty, $($argname: $argtype),*) $(-> $ret)? {
            match $seif {
                $tinyname::Inline(i) => i.$fname($($argname),*),
                $tinyname::Heap(h) => h.$fname($($argname),*),
            }
        }
        )*
    };
}

impl<A: Array> TinyVecDeq<A> {
    impl_mirrored! {
        type Mirror = TinyVecDeq;

        pub fn len(self: &Self) -> usize;
        pub fn is_empty(self: &Self) -> bool;
        pub fn clear(self: &mut Self);
        pub fn capacity(self: &Self) -> usize;
        pub fn remove(self: &mut Self, index: usize) -> Option<A::Item>;
        pub fn make_contiguous(self: &mut Self) -> &mut [A::Item];
        pub fn get(self: &Self, index: usize) -> Option<&A::Item>;
        pub fn get_mut(self: &mut Self, index: usize) -> Option<&mut A::Item>;
        pub fn as_slices(self: &Self) -> (&[A::Item], &[A::Item]);
        pub fn as_mut_slices(self: &mut Self) -> (&mut [A::Item], &mut [A::Item]);
        pub fn front(self: &Self) -> Option<&A::Item>;
        pub fn back(self: &Self) -> Option<&A::Item>;
        pub fn front_mut(self: &mut Self) -> Option<&mut A::Item>;
        pub fn back_mut(self: &mut Self) -> Option<&mut A::Item>;
        pub fn pop_front(self: &mut Self) -> Option<A::Item>;
        pub fn pop_back(self: &mut Self) -> Option<A::Item>;
        pub fn swap_remove_front(self: &mut Self, index: usize) -> Option<A::Item>;
        pub fn swap_remove_back(self: &mut Self, index: usize) -> Option<A::Item>;
        pub fn swap(self: &mut Self, a: usize, b: usize);
    }

    pub fn append(&mut self, other: &mut Self)
    where
        A::Item: Clone,
    {
        self.reserve(other.len());
        match (self, other) {
            (TinyVecDeq::Heap(a), TinyVecDeq::Heap(b)) => {
                a.append(b);
            },
            (TinyVecDeq::Inline(a), TinyVecDeq::Heap(b)) => a.extend(b.drain(..)),
            (ref mut this, TinyVecDeq::Inline(b)) => {
                this.extend(b.drain(..));
            },
        };
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &A::Item> {
        match self {
            TinyVecDeq::Inline(v) => Either::Left(v.iter()),
            TinyVecDeq::Heap(v) => Either::Right(v.iter()),
        }
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = &mut A::Item> {
        match self {
            TinyVecDeq::Inline(v) => Either::Left(v.iter_mut()),
            TinyVecDeq::Heap(v) => Either::Right(v.iter_mut()),
        }
    }

    pub fn drain<R>(&mut self, range: R) -> impl Iterator<Item = A::Item> + '_
    where
        R: RangeBounds<usize>,
    {
        match self {
            TinyVecDeq::Inline(v) => Either::Left(v.drain(range)),
            TinyVecDeq::Heap(v) => Either::Right(v.drain(range)),
        }
    }

    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut A::Item) -> bool,
    {
        match self {
            TinyVecDeq::Inline(v) => v.retain_mut(f),
            TinyVecDeq::Heap(v) => v.retain_mut(f),
        }
    }

    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&A::Item) -> bool,
    {
        match self {
            TinyVecDeq::Inline(v) => v.retain(f),
            TinyVecDeq::Heap(v) => v.retain(f),
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let inner = match self {
            TinyVecDeq::Inline(v) => v,
            TinyVecDeq::Heap(v) => return v.reserve(additional),
        };
        if additional > inner.capacity() - inner.len() {
            let v = inner.drain_to_vec_and_reserve(additional);
            *self = TinyVecDeq::Heap(v);
        }
    }

    pub fn push_front(&mut self, value: A::Item) {
        self.reserve(1);
        match self {
            TinyVecDeq::Inline(v) => v.push_front(value),
            TinyVecDeq::Heap(v) => v.push_front(value),
        }
    }

    pub fn push_back(&mut self, value: A::Item) {
        self.reserve(1);
        match self {
            TinyVecDeq::Inline(v) => v.push_back(value),
            TinyVecDeq::Heap(v) => v.push_back(value),
        }
    }

    pub fn insert(&mut self, index: usize, element: A::Item) {
        self.reserve(1);
        match self {
            TinyVecDeq::Inline(v) => v.insert(index, element),
            TinyVecDeq::Heap(v) => v.insert(index, element),
        }
    }

    pub fn shrink_to_fit(&mut self) {
        match self {
            TinyVecDeq::Inline(_) => (),
            TinyVecDeq::Heap(vec) => {
                if vec.len() > A::CAPACITY {
                    return vec.shrink_to_fit()
                }
                let mut n = ArrayVecDeq::default();
                n.extend(vec.drain(..));
                *self = TinyVecDeq::Inline(n);
            },
        }
    }

    pub fn move_to_the_heap(&mut self) {
        match self {
            TinyVecDeq::Inline(arr) => {
                let vec = arr.drain_to_vec_and_reserve(0);
                *self = TinyVecDeq::Heap(vec);
            },
            TinyVecDeq::Heap(_) => (),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= A::CAPACITY {
            TinyVecDeq::Inline(ArrayVecDeq::default())
        } else {
            TinyVecDeq::Heap(VecDeque::with_capacity(capacity))
        }
    }

    pub fn new(arr: A) -> Self {
        TinyVecDeq::Inline(ArrayVecDeq::new(arr))
    }
}

impl<A: Array> Extend<A::Item> for TinyVecDeq<A> {
    fn extend<T: IntoIterator<Item = A::Item>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        match self {
            TinyVecDeq::Inline(v) => v.extend(iter),
            TinyVecDeq::Heap(v) => v.extend(iter),
        }
    }
}

impl<A: Array> std::fmt::Debug for TinyVecDeq<A>
where
    A::Item: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TinyVecDeq::Inline(v) => v.fmt(f),
            TinyVecDeq::Heap(v) => v.fmt(f),
        }
    }
}

impl<A: Array, const N: usize> PartialEq<[A::Item; N]> for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &[A::Item; N]) -> bool {
        match self {
            TinyVecDeq::Inline(v) => v.eq(other),
            TinyVecDeq::Heap(v) => v.eq(other),
        }
    }
}
impl<A: Array, const N: usize> PartialEq<&[A::Item; N]> for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &&[A::Item; N]) -> bool {
        match self {
            TinyVecDeq::Inline(v) => v.eq(other),
            TinyVecDeq::Heap(v) => v.eq(other),
        }
    }
}
impl<A: Array, const N: usize> PartialEq<&mut [A::Item; N]> for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &&mut [A::Item; N]) -> bool {
        match self {
            TinyVecDeq::Inline(v) => v.eq(other),
            TinyVecDeq::Heap(v) => v.eq(other),
        }
    }
}
impl<A: Array> PartialEq<&mut [A::Item]> for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &&mut [A::Item]) -> bool {
        match self {
            TinyVecDeq::Inline(v) => v.eq(other),
            TinyVecDeq::Heap(v) => v.eq(other),
        }
    }
}
impl<A: Array> PartialEq<Vec<A::Item>> for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &Vec<A::Item>) -> bool {
        match self {
            TinyVecDeq::Inline(v) => v.eq(other),
            TinyVecDeq::Heap(v) => v.eq(other),
        }
    }
}

impl<A: Array> PartialEq for TinyVecDeq<A>
where
    A::Item: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TinyVecDeq::Inline(v1), TinyVecDeq::Inline(v2)) => v1.eq(v2),
            (TinyVecDeq::Heap(v1), TinyVecDeq::Heap(v2)) => v1.eq(v2),
            (TinyVecDeq::Inline(v1), TinyVecDeq::Heap(v2)) => v1.eq(v2),
            (TinyVecDeq::Heap(v1), TinyVecDeq::Inline(v2)) => v2.eq(v1),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    /// Check if unused elements are initialized to the default value.
    fn check_spare<A>(v: &TinyVecDeq<A>)
    where
        A: Array,
        A::Item: Default + PartialEq + std::fmt::Debug,
    {
        match v {
            TinyVecDeq::Inline(v) => crate::arrayvecdeq::check_spare(v),
            TinyVecDeq::Heap(_) => (),
        }
    }

    crate::gen_tests!(TinyVecDeq);

    #[test]
    fn test_push_back_overflow() {
        let mut tester = TinyVecDeq::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);
        tester.push_back(4);
        assert_eq!(tester, [1, 2, 3, 4]);
    }

    #[test]
    fn test_push_front_overflow() {
        let mut tester = TinyVecDeq::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);
        tester.push_front(4);
        assert_eq!(tester, [4, 1, 2, 3]);
    }

    #[test]
    fn test_insert_overflow() {
        let mut tester = TinyVecDeq::new([0; 3]);
        tester.push_back(1);
        tester.push_back(2);
        tester.push_back(3);
        tester.insert(2, 4);
        assert_eq!(tester, [1, 2, 4, 3]);
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
        for len in minlen..CAP * 2 {
            // 0, 1, 2, .., len - 1
            let expected: Vec<_> = (0..).take(len).collect();
            for to_remove in 0..=len {
                let mut tester = TinyVecDeq::new([0; CAP]);
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
                assert_eq!(tester, expected);
                check_spare(&tester);
            }
        }
    }
}
