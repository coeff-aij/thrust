//! Code of the case study that is not rustc's: the iterator adapters of rewrites.md R8 and
//! `SliceIter::find` of R9, the `Model` declarations, specifications of std functions and the
//! lemmas of the drafts.

use crate::thrust_models;

pub mod iter;
pub mod lemmas;
pub mod models;
pub mod std_specs;

/// The model of `usize` and `u64`, which carries its width while `THRUST_INT_RANGE` is set.
#[cfg(not(thrust_int_range))]
pub type USize = thrust_models::model::UInt;
#[cfg(thrust_int_range)]
pub type USize = thrust_models::model::UIntN<64>;
