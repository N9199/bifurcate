#![deny(clippy::incompatible_msrv, clippy::todo)]
#![warn(
    rust_2024_compatibility,
    clippy::perf,
    clippy::complexity,
    clippy::cargo,
    clippy::pedantic,
    clippy::absolute_paths,
    clippy::alloc_instead_of_core,
    clippy::allow_attributes_without_reason,
    clippy::dbg_macro,
    clippy::std_instead_of_core,
    clippy::undocumented_unsafe_blocks,
    clippy::unnecessary_safety_comment,
    clippy::unnecessary_self_imports,
    clippy::unused_self,
    clippy::wildcard_imports,
    clippy::used_underscore_binding,
    clippy::struct_field_names,
    clippy::cognitive_complexity,
    clippy::debug_assert_with_mut_call,
    clippy::use_self
)]
//! # Bifurcate
//! This is a small crate with the only purpose to provide and efficient and really general
//! implementation of [`bisect_left`], [`bisect_right`] and [`equal_range`] for some obvious types,
//! while also giving the possibility of other types using the implementation.
//! 
//! [`bisect_left`]: Bisectable::bisect_left
//! [`bisect_right`]: Bisectable::bisect_right
//! [`equal_range`]: Bisectable::equal_range
//! 
//! The main trait, [`Bisectable`], is implemented for [`Range`], [`slice`] and [`array`] as a convenience. 
//! Also, the [`slice`] implementation can serve as a simple implementation blueprint for other types.
//! 
//! [`Range`]: std::ops::Range
//! 
//! ## Note
//! This crate polyfills the [`Step`] trait, as it's unstable see [#42168](https://github.com/rust-lang/rust/issues/42168). 
//! This can be disabled via the `nightly_step` feature flag.
//! 
//! Related to the above, there's the `nightly_ascii` feature flag, which enables the implementation for [`Step`] 
//! for the nightly only [`AsciiChar`], see [#110998](https://github.com/rust-lang/rust/issues/110998), 
//! which also implements the nightly only trait [`Step`].
//! 
//! [`AsciiChar`]:  core::ascii::Char
mod bisectable_impls;
mod nightly_polyfill;
mod traits;

pub use traits::{Bisectable, MidPoint};
#[cfg(feature = "nightly_step")]
pub use core::iter::Step;
#[cfg(not(feature = "nightly_step"))]
pub use nightly_polyfill::Step;

