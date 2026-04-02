use std::mem::MaybeUninit;

/// A trait for types that are an array.
///
/// An "array", for our purposes, has the following properties:
/// * Owns some number of elements.
/// * The element type can be generic, but must implement [`Default`].
/// * The capacity is fixed at compile time, based on the implementing type.
/// * You can get a shared or mutable slice to the elements.
///
/// You are generally **not** expected to need to implement this yourself. It is
/// already implemented for all the major array lengths (`0..=32` and the powers
/// of 2 up to 4,096), or for all array lengths with the feature `rustc_1_55`.
///
/// **Additional lengths can easily be added upon request.**
///
/// ## Safety
///
/// The slices returned by `as_slice`, `as_slice_mut`, and `transpose_uninit`
/// must contain exactly `CAPACITY` elements.
pub unsafe trait Array {
    /// The type of the items in the thing.
    type Item;

    /// The number of slots in the thing.
    const CAPACITY: usize;

    /// Gives a shared slice over the whole thing.
    ///
    /// A correct implementation will return a slice with a length equal to the
    /// `CAPACITY` value.
    #[must_use]
    fn as_slice(&self) -> &[Self::Item];

    /// Gives a unique slice over the whole thing.
    ///
    /// A correct implementation will return a slice with a length equal to the
    /// `CAPACITY` value.
    #[must_use]
    fn as_slice_mut(&mut self) -> &mut [Self::Item];

    /// Transpose a `MaybeUninit<[T; N]>` to a `[MaybeUninit<T>]`.
    fn transpose_uninit_mut(arr: &mut MaybeUninit<Self>) -> &mut [MaybeUninit<Self::Item>]
    where
        Self: Sized;

    /// Transpose a `MaybeUninit<[T; N]>` to a `[MaybeUninit<T>]`.
    fn transpose_uninit(arr: &MaybeUninit<Self>) -> &[MaybeUninit<Self::Item>]
    where
        Self: Sized;
}

unsafe impl<T, const N: usize> Array for [T; N] {
    type Item = T;

    const CAPACITY: usize = N;

    #[inline(always)]
    fn as_slice(&self) -> &[T] {
        self
    }

    #[inline(always)]
    fn as_slice_mut(&mut self) -> &mut [T] {
        &mut *self
    }

    #[inline(always)]
    fn transpose_uninit_mut(arr: &mut MaybeUninit<[T; N]>) -> &mut [MaybeUninit<T>]
    where
        Self: Sized,
    {
        unsafe { std::slice::from_raw_parts_mut(arr.as_mut_ptr() as _, N) }
    }

    #[inline(always)]
    fn transpose_uninit(arr: &MaybeUninit<[T; N]>) -> &[MaybeUninit<T>]
    where
        Self: Sized,
    {
        unsafe { std::slice::from_raw_parts(arr.as_ptr() as _, N) }
    }
}
