#[cfg(feature = "nightly")]
use core::ascii::Char as AsciiChar;
use core::convert::TryFrom;
use core::net::{Ipv4Addr, Ipv6Addr};

// // Safety: All invariants are upheld.
// macro_rules! unsafe_impl_trusted_step {
//     ($($type:ty)*) => {$(
//         unsafe impl TrustedStep for $type {}
//     )*};
// }
// unsafe_impl_trusted_step![AsciiChar char i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize Ipv4Addr Ipv6Addr];

/// Objects that have a notion of *successor* and *predecessor* operations.
///
/// This is essentially a stable polyfill of the nightly [`Step`](core::iter::Step) trait, 
/// you can disable it's use by using the `nightly_step` feature which enables dependance 
/// on the std version of the trait instead of this polyfill. There's also the unsafe marker trait
/// [`TrustedStep`](core::iter::TrustedStep) that's used for specialization which we **can't** polyfill.
///
/// The *successor* operation moves towards values that compare greater.
/// The *predecessor* operation moves towards values that compare lesser.
pub trait Step: Clone + PartialOrd + Sized {
    /// Returns the number of *successor* steps required to get from `start` to `end`.
    ///
    /// Returns `None` if the number of steps would overflow `usize`
    /// (or is infinite, or if `end` would never be reached).
    ///
    /// # Invariants
    ///
    /// For any `a`, `b`, and `n`:
    ///
    /// * `steps_between(&a, &b) == Some(n)` if and only if `Step::forward_checked(&a, n) == Some(b)`
    /// * `steps_between(&a, &b) == Some(n)` if and only if `Step::backward_checked(&b, n) == Some(a)`
    /// * `steps_between(&a, &b) == Some(n)` only if `a <= b`
    ///   * Corollary: `steps_between(&a, &b) == Some(0)` if and only if `a == b`
    ///   * Note that `a <= b` does _not_ imply `steps_between(&a, &b) != None`;
    ///     this is the case when it would require more than `usize::MAX` steps to get to `b`
    /// * `steps_between(&a, &b) == None` if `a > b`
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`, returns `None`.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`:
    ///
    /// * `Step::forward_checked(a, n).and_then(|x| Step::forward_checked(x, m)) == Step::forward_checked(a, m).and_then(|x| Step::forward_checked(x, n))`
    ///
    /// For any `a`, `n`, and `m` where `n + m` does not overflow:
    ///
    /// * `Step::forward_checked(a, n).and_then(|x| Step::forward_checked(x, m)) == Step::forward_checked(a, n + m)`
    ///
    /// For any `a` and `n`:
    ///
    /// * `Step::forward_checked(a, n) == (0..n).try_fold(a, |x, _| Step::forward_checked(&x, 1))`
    ///   * Corollary: `Step::forward_checked(&a, 0) == Some(a)`
    fn forward_checked(start: Self, count: usize) -> Option<Self>;

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// this function is allowed to panic, wrap, or saturate.
    /// The suggested behavior is to panic when debug assertions are enabled,
    /// and to wrap or saturate otherwise.
    ///
    /// Unsafe code should not rely on the correctness of behavior after overflow.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`, where no overflow occurs:
    ///
    /// * `Step::forward(Step::forward(a, n), m) == Step::forward(a, n + m)`
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::forward_checked(a, n) == Some(Step::forward(a, n))`
    /// * `Step::forward(a, n) == (0..n).fold(a, |x, _| Step::forward(x, 1))`
    ///   * Corollary: `Step::forward(a, 0) == a`
    /// * `Step::forward(a, n) >= a`
    /// * `Step::backward(Step::forward(a, n), n) == a`
    fn forward(start: Self, count: usize) -> Self {
        Step::forward_checked(start, count).expect("overflow in `Step::forward`")
    }

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// # Safety
    ///
    /// It is undefined behavior for this operation to overflow the
    /// range of values supported by `Self`. If you cannot guarantee that this
    /// will not overflow, use `forward` or `forward_checked` instead.
    ///
    /// # Invariants
    ///
    /// For any `a`:
    ///
    /// * if there exists `b` such that `b > a`, it is safe to call `Step::forward_unchecked(a, 1)`
    /// * if there exists `b`, `n` such that `steps_between(&a, &b) == Some(n)`,
    ///   it is safe to call `Step::forward_unchecked(a, m)` for any `m <= n`.
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::forward_unchecked(a, n)` is equivalent to `Step::forward(a, n)`
    unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }

    /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`, returns `None`.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`:
    ///
    /// * `Step::backward_checked(a, n).and_then(|x| Step::backward_checked(x, m)) == n.checked_add(m).and_then(|x| Step::backward_checked(a, x))`
    /// * `Step::backward_checked(a, n).and_then(|x| Step::backward_checked(x, m)) == try { Step::backward_checked(a, n.checked_add(m)?) }`
    ///
    /// For any `a` and `n`:
    ///
    /// * `Step::backward_checked(a, n) == (0..n).try_fold(a, |x, _| Step::backward_checked(&x, 1))`
    ///   * Corollary: `Step::backward_checked(&a, 0) == Some(a)`
    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// this function is allowed to panic, wrap, or saturate.
    /// The suggested behavior is to panic when debug assertions are enabled,
    /// and to wrap or saturate otherwise.
    ///
    /// Unsafe code should not rely on the correctness of behavior after overflow.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`, where no overflow occurs:
    ///
    /// * `Step::backward(Step::backward(a, n), m) == Step::backward(a, n + m)`
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::backward_checked(a, n) == Some(Step::backward(a, n))`
    /// * `Step::backward(a, n) == (0..n).fold(a, |x, _| Step::backward(x, 1))`
    ///   * Corollary: `Step::backward(a, 0) == a`
    /// * `Step::backward(a, n) <= a`
    /// * `Step::forward(Step::backward(a, n), n) == a`
    fn backward(start: Self, count: usize) -> Self {
        Step::backward_checked(start, count).expect("overflow in `Step::backward`")
    }

    /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// # Safety
    ///
    /// It is undefined behavior for this operation to overflow the
    /// range of values supported by `Self`. If you cannot guarantee that this
    /// will not overflow, use `backward` or `backward_checked` instead.
    ///
    /// # Invariants
    ///
    /// For any `a`:
    ///
    /// * if there exists `b` such that `b < a`, it is safe to call `Step::backward_unchecked(a, 1)`
    /// * if there exists `b`, `n` such that `steps_between(&b, &a) == Some(n)`,
    ///   it is safe to call `Step::backward_unchecked(a, m)` for any `m <= n`.
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::backward_unchecked(a, n)` is equivalent to `Step::backward(a, n)`
    unsafe fn backward_unchecked(start: Self, count: usize) -> Self {
        Step::backward(start, count)
    }
}

// These are still macro-generated because the integer literals resolve to different types.
macro_rules! step_identical_methods {
    () => {
        #[inline]
        unsafe fn forward_unchecked(start: Self, n: usize) -> Self {
            // SAFETY: the caller has to guarantee that `start + n` doesn't overflow.
            unsafe { start.unchecked_add(n as Self) }
        }

        #[inline]
        unsafe fn backward_unchecked(start: Self, n: usize) -> Self {
            // SAFETY: the caller has to guarantee that `start - n` doesn't overflow.
            unsafe { start.unchecked_sub(n as Self) }
        }

        /// Rustc magic will be lost
        #[inline]
        #[allow(arithmetic_overflow)]
        fn forward(start: Self, n: usize) -> Self {
            // In debug builds, trigger a panic on overflow.
            // This should optimize completely out in release builds.
            if Self::forward_checked(start, n).is_none() {
                let _ = Self::MAX + 1;
            }
            // Do wrapping math to allow e.g. `Step::forward(-128i8, 255)`.
            start.wrapping_add(n as Self)
        }

        /// Rustc magic will be lost
        #[inline]
        #[allow(arithmetic_overflow)]
        fn backward(start: Self, n: usize) -> Self {
            // In debug builds, trigger a panic on overflow.
            // This should optimize completely out in release builds.
            if Self::backward_checked(start, n).is_none() {
                let _ = Self::MIN - 1;
            }
            // Do wrapping math to allow e.g. `Step::backward(127i8, 255)`.
            start.wrapping_sub(n as Self)
        }
    };
}

macro_rules! step_integer_impls {
    {
        narrower than or same width as usize:
            $( [ $u_narrower:ident $i_narrower:ident ] ),+;
        wider than usize:
            $( [ $u_wider:ident $i_wider:ident ] ),+;
    } => {
        $(
            impl Step for $u_narrower {
                step_identical_methods!();

                #[inline]
                fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                    if *start <= *end {
                        // This relies on $u_narrower <= usize
                        Some((*end - *start) as usize)
                    } else {
                        None
                    }
                }

                #[inline]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    match Self::try_from(n) {
                        Ok(n) => start.checked_add(n),
                        Err(_) => None, // if n is out of range, `unsigned_start + n` is too
                    }
                }

                #[inline]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    match Self::try_from(n) {
                        Ok(n) => start.checked_sub(n),
                        Err(_) => None, // if n is out of range, `unsigned_start - n` is too
                    }
                }
            }

            #[allow(unreachable_patterns)]
            impl Step for $i_narrower {
                step_identical_methods!();

                #[inline]
                fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                    if *start <= *end {
                        // This relies on $i_narrower <= usize
                        //
                        // Casting to isize extends the width but preserves the sign.
                        // Use wrapping_sub in isize space and cast to usize to compute
                        // the difference that might not fit inside the range of isize.
                        Some((*end as isize).wrapping_sub(*start as isize) as usize)
                    } else {
                        None
                    }
                }

                #[inline]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_add(n as Self);
                            if wrapped >= start {
                                Some(wrapped)
                            } else {
                                None // Addition overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 + n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }

                #[inline]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_sub(n as Self);
                            if wrapped <= start {
                                Some(wrapped)
                            } else {
                                None // Subtraction overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 - n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }
            }
        )+

        $(
            #[allow(unreachable_patterns)]
            impl Step for $u_wider {
                step_identical_methods!();

                #[inline]
                fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                    if *start <= *end {
                        usize::try_from(*end - *start).ok()
                    } else {
                        None
                    }
                }

                #[inline]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_add(n as Self)
                }

                #[inline]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_sub(n as Self)
                }
            }

            impl Step for $i_wider {
                step_identical_methods!();

                #[inline]
                fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                    if *start <= *end {
                        match end.checked_sub(*start) {
                            Some(result) => usize::try_from(result).ok(),
                            // If the difference is too big for e.g. i128,
                            // it's also gonna be too big for usize with fewer bits.
                            None => None,
                        }
                    } else {
                        None
                    }
                }

                #[inline]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_add(n as Self)
                }

                #[inline]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_sub(n as Self)
                }
            }
        )+
    };
}

#[cfg(target_pointer_width = "64")]
step_integer_impls! {
    narrower than or same width as usize: [u8 i8], [u16 i16], [u32 i32], [u64 i64], [usize isize];
    wider than usize: [u128 i128];
}

#[cfg(target_pointer_width = "32")]
step_integer_impls! {
    narrower than or same width as usize: [u8 i8], [u16 i16], [u32 i32], [usize isize];
    wider than usize: [u64 i64], [u128 i128];
}

#[cfg(target_pointer_width = "16")]
step_integer_impls! {
    narrower than or same width as usize: [u8 i8], [u16 i16], [usize isize];
    wider than usize: [u32 i32], [u64 i64], [u128 i128];
}

impl Step for char {
    #[inline]
    fn steps_between(&start: &char, &end: &char) -> Option<usize> {
        let start = start as u32;
        let end = end as u32;
        if start <= end {
            let count = end - start;
            if start < 0xD800 && 0xE000 <= end {
                usize::try_from(count - 0x800).ok()
            } else {
                usize::try_from(count).ok()
            }
        } else {
            None
        }
    }

    #[inline]
    fn forward_checked(start: char, count: usize) -> Option<char> {
        let start = start as u32;
        let mut res = Step::forward_checked(start, count)?;
        if start < 0xD800 && 0xD800 <= res {
            res = Step::forward_checked(res, 0x800)?;
        }
        if res <= char::MAX as u32 {
            // SAFETY: res is a valid unicode scalar
            // (below 0x110000 and not in 0xD800..0xE000)
            Some(unsafe { char::from_u32_unchecked(res) })
        } else {
            None
        }
    }

    #[inline]
    fn backward_checked(start: char, count: usize) -> Option<char> {
        let start = start as u32;
        let mut res = Step::backward_checked(start, count)?;
        if start >= 0xE000 && 0xE000 > res {
            res = Step::backward_checked(res, 0x800)?;
        }
        // SAFETY: res is a valid unicode scalar
        // (below 0x110000 and not in 0xD800..0xE000)
        Some(unsafe { char::from_u32_unchecked(res) })
    }

    #[inline]
    unsafe fn forward_unchecked(start: char, count: usize) -> char {
        let start = start as u32;
        // SAFETY: the caller must guarantee that this doesn't overflow
        // the range of values for a char.
        let mut res = unsafe { Step::forward_unchecked(start, count) };
        if start < 0xD800 && 0xD800 <= res {
            // SAFETY: the caller must guarantee that this doesn't overflow
            // the range of values for a char.
            res = unsafe { Step::forward_unchecked(res, 0x800) };
        }
        // SAFETY: because of the previous contract, this is guaranteed
        // by the caller to be a valid char.
        unsafe { char::from_u32_unchecked(res) }
    }

    #[inline]
    unsafe fn backward_unchecked(start: char, count: usize) -> char {
        let start = start as u32;
        // SAFETY: the caller must guarantee that this doesn't overflow
        // the range of values for a char.
        let mut res = unsafe { Step::backward_unchecked(start, count) };
        if start >= 0xE000 && 0xE000 > res {
            // SAFETY: the caller must guarantee that this doesn't overflow
            // the range of values for a char.
            res = unsafe { Step::backward_unchecked(res, 0x800) };
        }
        // SAFETY: because of the previous contract, this is guaranteed
        // by the caller to be a valid char.
        unsafe { char::from_u32_unchecked(res) }
    }
}

#[cfg(feature = "nightly")]
impl Step for AsciiChar {
    #[inline]
    fn steps_between(&start: &AsciiChar, &end: &AsciiChar) -> Option<usize> {
        Step::steps_between(&start.to_u8(), &end.to_u8())
    }

    #[inline]
    fn forward_checked(start: AsciiChar, count: usize) -> Option<AsciiChar> {
        let end = Step::forward_checked(start.to_u8(), count)?;
        AsciiChar::from_u8(end)
    }

    #[inline]
    fn backward_checked(start: AsciiChar, count: usize) -> Option<AsciiChar> {
        let end = Step::backward_checked(start.to_u8(), count)?;

        // SAFETY: Values below that of a valid ASCII character are also valid ASCII
        Some(unsafe { AsciiChar::from_u8_unchecked(end) })
    }

    #[inline]
    unsafe fn forward_unchecked(start: AsciiChar, count: usize) -> AsciiChar {
        // SAFETY: Caller asserts that result is a valid ASCII character,
        // and therefore it is a valid u8.
        let end = unsafe { Step::forward_unchecked(start.to_u8(), count) };

        // SAFETY: Caller asserts that result is a valid ASCII character.
        unsafe { AsciiChar::from_u8_unchecked(end) }
    }

    #[inline]
    unsafe fn backward_unchecked(start: AsciiChar, count: usize) -> AsciiChar {
        // SAFETY: Caller asserts that result is a valid ASCII character,
        // and therefore it is a valid u8.
        let end = unsafe { Step::backward_unchecked(start.to_u8(), count) };

        // SAFETY: Caller asserts that result is a valid ASCII character.
        unsafe { AsciiChar::from_u8_unchecked(end) }
    }
}

impl Step for Ipv4Addr {
    #[inline]
    fn steps_between(&start: &Ipv4Addr, &end: &Ipv4Addr) -> Option<usize> {
        u32::steps_between(&start.to_bits(), &end.to_bits())
    }

    #[inline]
    fn forward_checked(start: Ipv4Addr, count: usize) -> Option<Ipv4Addr> {
        u32::forward_checked(start.to_bits(), count).map(Ipv4Addr::from_bits)
    }

    #[inline]
    fn backward_checked(start: Ipv4Addr, count: usize) -> Option<Ipv4Addr> {
        u32::backward_checked(start.to_bits(), count).map(Ipv4Addr::from_bits)
    }

    #[inline]
    unsafe fn forward_unchecked(start: Ipv4Addr, count: usize) -> Ipv4Addr {
        // SAFETY: Since u32 and Ipv4Addr are losslessly convertible,
        //   this is as safe as the u32 version.
        Ipv4Addr::from_bits(unsafe { u32::forward_unchecked(start.to_bits(), count) })
    }

    #[inline]
    unsafe fn backward_unchecked(start: Ipv4Addr, count: usize) -> Ipv4Addr {
        // SAFETY: Since u32 and Ipv4Addr are losslessly convertible,
        //   this is as safe as the u32 version.
        Ipv4Addr::from_bits(unsafe { u32::backward_unchecked(start.to_bits(), count) })
    }
}

impl Step for Ipv6Addr {
    #[inline]
    fn steps_between(&start: &Ipv6Addr, &end: &Ipv6Addr) -> Option<usize> {
        u128::steps_between(&start.to_bits(), &end.to_bits())
    }

    #[inline]
    fn forward_checked(start: Ipv6Addr, count: usize) -> Option<Ipv6Addr> {
        u128::forward_checked(start.to_bits(), count).map(Ipv6Addr::from_bits)
    }

    #[inline]
    fn backward_checked(start: Ipv6Addr, count: usize) -> Option<Ipv6Addr> {
        u128::backward_checked(start.to_bits(), count).map(Ipv6Addr::from_bits)
    }

    #[inline]
    unsafe fn forward_unchecked(start: Ipv6Addr, count: usize) -> Ipv6Addr {
        // SAFETY: Since u128 and Ipv6Addr are losslessly convertible,
        //   this is as safe as the u128 version.
        Ipv6Addr::from_bits(unsafe { u128::forward_unchecked(start.to_bits(), count) })
    }

    #[inline]
    unsafe fn backward_unchecked(start: Ipv6Addr, count: usize) -> Ipv6Addr {
        // SAFETY: Since u128 and Ipv6Addr are losslessly convertible,
        //   this is as safe as the u128 version.
        Ipv6Addr::from_bits(unsafe { u128::backward_unchecked(start.to_bits(), count) })
    }
}
