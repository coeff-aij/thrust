//! Code of the case study that is not rustc's: the iterator adapters of rewrites.md R8, the
//! `Model` declarations, specifications of std functions and the lemmas of the drafts.

use crate::thrust_models;

pub mod iter;
pub mod counts;
pub mod lemmas;
pub mod models;
pub mod std_specs;
pub mod weights;

/// The model of `usize` and `u64`, which carries its width while `THRUST_INT_RANGE` is set.
#[cfg(not(thrust_int_range))]
pub type USize = thrust_models::model::UInt;
#[cfg(thrust_int_range)]
pub type USize = thrust_models::model::UIntN<64>;

/// `tracing`'s `debug!` and `trace!`, which rustc's code calls; they do nothing, as with logging
/// off, so that the calls stay as rustc has them.
pub mod tracing {
    macro_rules! debug {
        ($($t:tt)*) => {};
    }
    macro_rules! trace {
        ($($t:tt)*) => {};
    }
    pub(crate) use {debug, trace};
}
