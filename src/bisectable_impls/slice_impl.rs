use core::cmp::Ordering;

use crate::traits::Bisectable;

impl<'a, T> Bisectable for &'a [T] {
    type Index = usize;
    type Value = T;

    fn bisect_left_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get it's item
        range.bisect_left_by(|index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }

    fn bisect_right_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get it's item
        range.bisect_right_by(move |index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }

    fn equal_range_by<F>(&self, f: F) -> Option<(Self::Index, Self::Index)>
    where
        F: Fn(&Self::Value) -> Ordering,
    {
        let range = 0..self.len();
        // SAFETY: index is always contained in the range defined above, so it's always safe to get it's item
        range.equal_range_by(|index: &usize| f(unsafe { self.get_unchecked(*index) }))
    }
}
