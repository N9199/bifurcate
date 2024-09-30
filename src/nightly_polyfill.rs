// This whole module is a polyfill of unstable traits in std for stable, it's preferable that none of this are used
#[cfg(not(feature = "nightly_step"))]
pub use step::Step;

#[cfg(not(feature = "nightly_step"))]
mod step;
