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
mod bisectable_impls;
mod nightly_polyfill;
mod traits;

pub use traits::{Bisectable, MidPoint, Step};
