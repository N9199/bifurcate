use core::{cmp::Ordering, ops::Range};

use crate::traits::Bisectable;

impl<const N: usize, T> Bisectable for [T; N] {
    type Index = usize;
    type Value = T;

    #[inline]
    fn bisect_left_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get the item
        range.bisect_left_by(|index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }

    #[inline]
    fn bisect_right_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get the item
        range.bisect_right_by(move |index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }

    #[inline]
    fn equal_range_by<F>(&self, mut f: F) -> Option<Range<Self::Index>>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get the item
        range.equal_range_by(|index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }
}
