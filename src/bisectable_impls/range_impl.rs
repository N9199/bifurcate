use core::{cmp::Ordering, ops::Range};

use crate::traits::{Bisectable, MidPoint};

impl<T> Bisectable for Range<T>
where
    T: MidPoint,
{
    type Index = T;
    type Value = T;

    #[inline]
    fn bisect_left_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let mut left = self.start.clone();
        let mut right = self.end.clone();
        while left < right {
            let mid = T::mid_point(&left, &right)?;
            match f(&mid) {
                Ordering::Less => left = T::forward_checked(mid, 1)?,
                Ordering::Greater | Ordering::Equal => right = mid,
            }
        }
        Some(left)
    }

    #[inline]
    fn bisect_right_by<F>(&self, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let mut left = self.start.clone();
        let mut right = self.end.clone();
        while left < right {
            let mid = T::mid_point(&left, &right)?;
            match f(&mid) {
                Ordering::Less | Ordering::Equal => left = T::forward_checked(mid, 1)?,
                Ordering::Greater => right = mid,
            }
        }
        Some(left)
    }

    #[inline]
    fn equal_range_by<F>(&self, mut f: F) -> Option<Range<Self::Index>>
    where
        F: FnMut(&Self::Value) -> Ordering,
    {
        let mut left = self.start.clone();
        let mut right = self.end.clone();
        while left < right {
            let mid = T::mid_point(&left, &right)?;
            match f(&mid) {
                Ordering::Less => left = T::forward_checked(mid, 1)?,
                Ordering::Greater => right = mid,
                Ordering::Equal => {
                    let left = (left..(mid.clone())).bisect_left_by(&mut f)?;
                    let right = (T::forward_checked(mid, 1)?..right).bisect_right_by(&mut f)?;
                    return Some(left..right);
                }
            }
        }
        Some(left..right)
    }
}

#[cfg(test)]
mod tests {
    use super::Bisectable;

    #[test]
    fn simplest_range_bisect_left_test() {
        let r = 0..10;
        let value_to_search_for = 5;
        let f = |v: &i32| v.cmp(&value_to_search_for);
        let found = r.bisect_left_by(&f).unwrap();
        assert_eq!(found, value_to_search_for);
    }

    #[test]
    fn simplest_range_bisect_right_test() {
        let r = 0..10;
        let value_to_search_smallest_value_bigger_than_this = 5;
        let f = |v: &i32| v.cmp(&value_to_search_smallest_value_bigger_than_this);
        let found = r.bisect_right_by(&f).unwrap();
        assert_eq!(found, value_to_search_smallest_value_bigger_than_this + 1);
    }

    #[test]
    fn simplest_range_equal_range_test() {
        let r = 0..10;
        let value_to_search_smallest_value_bigger_than_this = 5;
        // [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        //                 ^  ^
        let start = 5;
        let end = 6;
        let found = r
            .equal_range_by(|v| v.cmp(&value_to_search_smallest_value_bigger_than_this))
            .unwrap();
        assert_eq!(found, start..end);
    }

    #[test]
    fn range_equal_range_more_than_one_element_is_equal_test() {
        let r = 0..20;
        let value_to_search_smallest_value_bigger_than_this = 5;
        // [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9]
        //                                ^     ^
        let start = 10;
        let end = 12;
        let found = r
            .equal_range_by(|v| (v / 2).cmp(&value_to_search_smallest_value_bigger_than_this))
            .unwrap();
        assert_eq!(found, start..end);
    }

    #[test]
    fn range_equal_range_no_element_equal_test() {
        let r = 0..5;
        let value_to_search_smallest_value_bigger_than_this = 5;
        // [0, 2, 4, 6, 8]
        //            ^
        let start = 3;
        let end = 3;
        let found = r
            .equal_range_by(|v| (v * 2).cmp(&value_to_search_smallest_value_bigger_than_this))
            .unwrap();
        assert_eq!(found, start..end);
    }
}
