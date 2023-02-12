use alloc::collections::VecDeque;

use crate::{array::Array, arrayvecdeq::ArrayVecDeq};

#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub enum TinyVecDeq<A: Array> {
    Inline(ArrayVecDeq<A>),
    Heap(VecDeque<A::Item>),
}
