#[repr(C)]
pub struct ArrayVecDeque<A> {
    array: A,
    head: usize,
    len: usize,
}

impl<A> Clone for ArrayVecDeque<A>
where
    A: Clone + tinyvec::Array,
    A::Item: Clone,
{
    fn clone(&self) -> Self {
        Self {
            array: self.array.clone(),
            head: self.head,
            len: self.len,
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

impl<A> ArrayVecDeque<A>
where
    A: tinyvec::Array,
{
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut A::Item> + '_ {
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        if first.len() >= self.len {
            first[..self.len].iter_mut().chain([].iter_mut())
        } else {
            let second_len = self.len - first.len();
            first.iter_mut().chain(second[..second_len].iter_mut())
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &A::Item> + '_ {
        let (second, first) = self.array.as_slice().split_at(self.head);
        if first.len() >= self.len {
            first[..self.len].iter().chain([].iter())
        } else {
            let second_len = self.len - first.len();
            first.iter().chain(second[..second_len].iter())
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn front(&self) -> Option<&A::Item> {
        if !self.is_empty() {
            self.array.as_slice().get(self.head)
        } else {
            None
        }
    }

    pub fn front_mut(&mut self) -> Option<&mut A::Item> {
        if !self.is_empty() {
            self.array.as_slice_mut().get_mut(self.head)
        } else {
            None
        }
    }

    pub fn back(&self) -> Option<&A::Item> {
        if !self.is_empty() {
            let index = (self.head + self.len - 1) % A::CAPACITY;
            self.array.as_slice().get(index)
        } else {
            None
        }
    }

    pub fn back_mut(&mut self) -> Option<&mut A::Item> {
        if !self.is_empty() {
            let index = (self.head + self.len - 1) % A::CAPACITY;
            self.array.as_slice_mut().get_mut(index)
        } else {
            None
        }
    }

    pub fn as_slices(&self) -> (&[A::Item], &[A::Item]) {
        let (second, first) = self.array.as_slice().split_at(self.head);
        if first.len() >= self.len {
            (first[..self.len].as_ref(), &[])
        } else {
            let second_len = self.len - first.len();
            (first, second[..second_len].as_ref())
        }
    }

    pub fn as_mut_slices(&mut self) -> (&mut [A::Item], &mut [A::Item]) {
        let (second, first) = self.array.as_slice_mut().split_at_mut(self.head);
        if first.len() >= self.len {
            (first[..self.len].as_mut(), &mut [])
        } else {
            let second_len = self.len - first.len();
            (first, second[..second_len].as_mut())
        }
    }

    pub fn capacity(&self) -> usize {
        A::CAPACITY
    }

    pub fn clear(&mut self) {
        for item in self.iter_mut() {
            *item = A::Item::default();
        }
        self.len = 0;
        self.head = 0;
    }

    pub fn drain(&mut self) -> impl Iterator<Item = A::Item> + '_ {
        struct Drain<'a, A: tinyvec::Array> {
            array: &'a mut [A::Item],
            head: &'a mut usize,
            len: &'a mut usize,
        }

        impl<A: tinyvec::Array> Iterator for Drain<'_, A> {
            type Item = A::Item;
            fn next(&mut self) -> Option<Self::Item> {
                if *self.len == 0 {
                    None
                } else {
                    let item = std::mem::take(self.array.get_mut(*self.head).unwrap());
                    *self.head = (*self.head + 1) % A::CAPACITY;
                    *self.len -= 1;
                    Some(item)
                }
            }
        }
        impl<A: tinyvec::Array> Drop for Drain<'_, A> {
            fn drop(&mut self) {
                self.for_each(|_| ());
                *self.head = 0;
            }
        }
        Drain::<A> {
            array: self.array.as_slice_mut(),
            head: &mut self.head,
            len: &mut self.len,
        }
    }

    pub fn get(&self, index: usize) -> Option<&A::Item> {
        if index < self.len {
            let index = (self.head + index) % A::CAPACITY;
            self.array.as_slice().get(index)
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut A::Item> {
        if index < self.len {
            let index = (self.head + index) % A::CAPACITY;
            self.array.as_slice_mut().get_mut(index)
        } else {
            None
        }
    }

    pub fn pop_back(&mut self) -> Option<A::Item> {
        if self.len == 0 {
            None
        } else {
            let index = (self.head + self.len - 1) % A::CAPACITY;
            let item = std::mem::take(self.array.as_slice_mut().get_mut(index).unwrap());
            self.len -= 1;
            Some(item)
        }
    }

    pub fn pop_front(&mut self) -> Option<A::Item> {
        if self.len == 0 {
            None
        } else {
            let item = std::mem::take(self.array.as_slice_mut().get_mut(self.head).unwrap());
            self.head = (self.head + 1) % A::CAPACITY;
            self.len -= 1;
            Some(item)
        }
    }

    pub fn try_push_back(&mut self, item: A::Item) -> Option<A::Item> {
        if self.len == A::CAPACITY {
            Some(item)
        } else {
            let index = (self.head + self.len) % A::CAPACITY;
            *self.array.as_slice_mut().get_mut(index).unwrap() = item;
            self.len += 1;
            None
        }
    }

    pub fn try_push_front(&mut self, item: A::Item) -> Option<A::Item> {
        if self.len == A::CAPACITY {
            Some(item)
        } else {
            self.head = (self.head + A::CAPACITY - 1) % A::CAPACITY;
            *self.array.as_slice_mut().get_mut(self.head).unwrap() = item;
            self.len += 1;
            None
        }
    }

    pub fn push_back(&mut self, item: A::Item) {
        let x = self.try_push_back(item);
        assert!(x.is_none(), "ArrayVecDeque capacity overflow");
    }

    pub fn push_front(&mut self, item: A::Item) {
        let x = self.try_push_front(item);
        assert!(x.is_none(), "ArrayVecDeque capacity overflow");
    }
}
