#[cfg(not(feature = "nightly_step"))]
pub use crate::nightly_polyfill::Step;
#[cfg(feature = "nightly_step")]
pub use core::iter::Step;

use core::cmp::Ordering;

/// Types that have a notion of *mid point* between two objects.
///
/// The *mid point* between two objects compares greater with the first object and lesser with the second object.
pub trait MidPoint: Step {
    /// Returns the value that would correspond to the midpoint between `start` and `end`, with preference to the "smallest" if there could be a tie, e.g. `mid_point(0, 1)` return `Some(0)`
    ///
    /// Returns `None` if the number of steps between star and end is infinite or if there's no midpoint
    ///
    /// # Invariants
    ///
    /// For any `a`, `b`, and `n`:
    ///
    /// * `mid_point(&a, &b) == Some(n)` if and only if `Step::forward_checked(&a, 2 * n) == Some(b)` or `Step::forward_checked(&a, 2 * n + 1) == Some(b)`
    /// * `mid_point(&a, &b) == Some(n)` if and only if `Step::backward_checked(&b, 2 * n) == Some(a)` or `Step::backward_checked(&b, 2 * n + 1) == Some(a)`
    /// * `mid_point(&a, &b) == Some(n)` only if `a <= b`
    ///   * Corollary: `mid_point(&a, &b) == Some(a)` if and only if `a == b` or `a == b + 1`
    ///   * Note that `a <= b` does _not_ imply `mid_point(&a, &b) != None`;
    ///     this is the case when it would require more than `2 * Self::MAX` steps to get to `b` //! TODO Recheck this documentation
    /// * `mid_point(&a, &b) == None` if `a > b`
    fn mid_point(start: &Self, end: &Self) -> Option<Self>;
}

macro_rules! mid_point_integer_impls {
    ($($type_name:ident),+) => {
        $(
        impl MidPoint for $type_name{
            fn mid_point(start: &Self, end: &Self) -> Option<Self>
            {
                let diff = end.checked_sub(*start)?;
                let half_step = diff/2; //Check this
                // SAFETY: start <= start + half_step <= end which guarantees that this give a valid output
                Some(unsafe{start.unchecked_add(half_step)})
            }
        })+
    };
}

mid_point_integer_impls!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize);

/// Types that can be searched via bisection either directly or indirectly.
pub trait Bisectable {
    /// `Value` corresponds to the type of inner values this type can be searched over.
    type Value;

    /// `Index` corresponds to the type by which this type can indexed in the general
    /// sense that there's an `i`-th value which itself of type `Value`
    /// and `i` is of type `Index`.
    type Index: MidPoint;

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a comparator function `f`.
    ///
    /// If the comparator function does not implement and order with the underlying order of the object,
    /// the return result is unspecified and meaningless.
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `f(a)` is either [`Ordering::Greater`] or [`Ordering::Equal`],
    /// and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_left`] and [`bisect_left_by_key`].
    ///
    /// [`bisect_left`]: Bisectable::bisect_left
    /// [`bisect_left_by_key`]: Bisectable::bisect_left_by_key
    ///
    /// # Examples
    ///
    /// Compares a series of three elements. The first is in the array and is unique,
    /// and as such the index returned is the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index of the first of the appearances. The third isn't in the array,
    /// and as such that the index where it would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [0, 1, 2, 3, 3, 3, 4, 6, 7];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_left_by(|probe| probe.cmp(&value)), Some(1));
    /// let value = 3;
    /// assert_eq!(s.bisect_left_by(|probe| probe.cmp(&value)), Some(3));
    /// let value = 5;
    /// assert_eq!(s.bisect_left_by(|probe| probe.cmp(&value)), Some(7));
    /// ```
    fn bisect_left_by<F>(&self, f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering;

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a given element `x`.
    /// If the type isn't sorted with respect of the order of [`Value`], the return result is unspecified and meaningless.
    ///
    /// [`Value`]: Bisectable::Value
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `a >= x`, and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_left_by`] and [`bisect_left_by_key`].
    ///
    /// [`bisect_left_by`]: Bisectable::bisect_left_by
    /// [`bisect_left_by_key`]: Bisectable::bisect_left_by_key
    ///
    /// # Examples
    ///
    /// Compares a series of three elements in a slice which is sorted. 
    /// The first is in the array and is unique,
    /// and as such the index returned is the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index of the first of the appearances. The third isn't in the array,
    /// and as such that the index where it would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [0, 1, 2, 3, 3, 3, 4, 6, 7];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_left(&value), Some(1));
    /// let value = 3;
    /// assert_eq!(s.bisect_left(&value), Some(3));
    /// let value = 5;
    /// assert_eq!(s.bisect_left(&value), Some(7));
    /// ```
    #[inline]
    fn bisect_left(&self, x: &Self::Value) -> Option<Self::Index>
    where
        Self::Value: Ord,
    {
        self.bisect_left_by(|v| v.cmp(x))
    }

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a given element `x` and a key extraction function `f`.
    /// If the type isn't sorted with respect of the order of [`Value`], the return result is unspecified and meaningless.
    ///
    /// [`Value`]: Bisectable::Value
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `f(a) >= x`, and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_left`] and [`bisect_left_by`].
    ///
    /// [`bisect_left`]: Bisectable::bisect_left
    /// [`bisect_left_by`]: Bisectable::bisect_left_by
    ///
    /// # Examples
    ///
    /// Compares a series of three elements in slice of pairs which is sorted by their second element. 
    /// The first is in the array and is unique,
    /// and as such the index returned is the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index of the first of the appearances. The third isn't in the array,
    /// and as such that the index where a pair with it as a second value
    /// would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [(4, 0), (3, 1), (1, 2), (3, 3), (15, 3), (6, 3), (4, 4), (9, 6), (3, 7)];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_left_by_key(&value, |&(a, b)| b), Some(1));
    /// let value = 3;
    /// assert_eq!(s.bisect_left_by_key(&value, |&(a, b)| b), Some(3));
    /// let value = 5;
    /// assert_eq!(s.bisect_left_by_key(&value, |&(a, b)| b), Some(7));
    /// ```
    #[inline]
    fn bisect_left_by_key<B, F>(&self, b: &B, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> B,
        B: Ord,
    {
        self.bisect_left_by(|v| f(v).cmp(b))
    }

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a comparator function `f`.
    ///
    /// If the comparator function does not implement and order with the underlying order of the object,
    /// the return result is unspecified and meaningless.
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `f(a)` is [`Ordering::Greater`], and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_right`] and [`bisect_right_by_key`].
    ///
    /// [`bisect_right`]: Bisectable::bisect_right
    /// [`bisect_right_by_key`]: Bisectable::bisect_right_by_key
    ///
    /// # Examples
    ///
    /// Compares a series of three elements. The first is in the array and is unique,
    /// and as such the index returned is the index after the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index just after the index of the last of the appearances. The third isn't in the array,
    /// and as such that the index where it would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [0, 1, 2, 3, 3, 3, 4, 6, 7];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_right_by(|probe| probe.cmp(&value)), Some(2));
    /// let value = 3;
    /// assert_eq!(s.bisect_right_by(|probe| probe.cmp(&value)), Some(6));
    /// let value = 5;
    /// assert_eq!(s.bisect_right_by(|probe| probe.cmp(&value)), Some(7));
    /// ```
    fn bisect_right_by<F>(&self, f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> Ordering;

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a given element `x`.
    /// If the type isn't sorted with respect of the order of [`Value`], the return result is unspecified and meaningless.
    ///
    /// [`Value`]: Bisectable::Value
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `a > x`, and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_right_by`] and [`bisect_right_by_key`].
    ///
    /// [`bisect_right_by`]: Bisectable::bisect_right_by
    /// [`bisect_right_by_key`]: Bisectable::bisect_right_by_key
    ///
    /// # Examples
    ///
    /// Compares a series of three elements in a slice which is sorted. 
    /// The first is in the array and is unique,
    /// and as such the index returned is the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index of the first of the appearances. The third isn't in the array,
    /// and as such that the index where it would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [0, 1, 2, 3, 3, 3, 4, 6, 7];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_right(&value), Some(2));
    /// let value = 3;
    /// assert_eq!(s.bisect_right(&value), Some(6));
    /// let value = 5;
    /// assert_eq!(s.bisect_right(&value), Some(7));
    /// ```
    #[inline]
    fn bisect_right(&self, x: &Self::Value) -> Option<Self::Index>
    where
        Self::Value: Ord,
    {
        self.bisect_right_by(|v| v.cmp(x))
    }

    // // Note that for types for which this crate implements MidPoint always return Some
    /// Bisects the type with a given element `x` and a key extraction function `f`.
    /// If the type isn't sorted with respect of the order of [`Value`], the return result is unspecified and meaningless.
    ///
    /// [`Value`]: Bisectable::Value
    ///
    /// If there the return value is [`Option::None`], then it means that either there's a pair of indices `i` and `j`,
    /// such that `mid_point(i, j) == None` or that there's an index `i` such that `forward_check(i, 1) == None`.
    /// See the documentation of [`Step`] and [`MidPoint`] for more information.
    ///
    /// If the return value is [`Option::Some`]`(i)`, then it means that `i` is such that the `i`-th value `a`
    /// satisfies that `f(a) > x`, and that `i` is the *least* index that satisfies that.
    ///
    /// See also [`bisect_right`] and [`bisect_right_by`].
    ///
    /// [`bisect_right`]: Bisectable::bisect_right
    /// [`bisect_right_by`]: Bisectable::bisect_right_by
    ///
    /// # Examples
    ///
    /// Compares a series of three elements in slice of pairs which is sorted by their second element. 
    /// The first is in the array and is unique,
    /// and as such the index returned is the index after the index of the element in the array.
    /// The second is in the array but there's multiple of them, and as such the index
    /// returned is the index after of the index of the last of the appearances. The third isn't in the array,
    /// and as such that the index where a pair with it as a second value
    /// would be inserted to maintain order is returned.
    ///
    /// ```
    /// # use bifurcate::Bisectable;
    /// let s = [(4, 0), (3, 1), (1, 2), (3, 3), (15, 3), (6, 3), (4, 4), (9, 6), (3, 7)];
    /// // Deref coercion doesn't work for arrays into slices?
    /// let s = s.as_ref();
    /// let value = 1;
    /// assert_eq!(s.bisect_right_by_key(&value, |&(a, b)| b), Some(2));
    /// let value = 3;
    /// assert_eq!(s.bisect_right_by_key(&value, |&(a, b)| b), Some(6));
    /// let value = 5;
    /// assert_eq!(s.bisect_right_by_key(&value, |&(a, b)| b), Some(7));
    /// ```
    #[inline]
    fn bisect_right_by_key<B, F>(&self, b: &B, mut f: F) -> Option<Self::Index>
    where
        F: FnMut(&Self::Value) -> B,
        B: Ord,
    {
        self.bisect_right_by(|v| f(v).cmp(b))
    }

    fn equal_range_by<F>(&self, f: F) -> Option<(Self::Index, Self::Index)>
    where
        F: FnMut(&Self::Value) -> Ordering;

    #[inline]
    fn equal_range(&self, x: &Self::Value) -> Option<(Self::Index, Self::Index)>
    where
        Self::Value: Ord,
    {
        self.equal_range_by(|v| v.cmp(x))
    }

    #[inline]
    fn equal_range_by_key<B, F>(&self, b: &B, mut f: F) -> Option<(Self::Index, Self::Index)>
    where
        F: FnMut(&Self::Value) -> B,
        B: Ord,
    {
        self.equal_range_by(|v| f(v).cmp(b))
    }
}
