//! Code of the case study that is not rustc's: the iterator adapters of rewrites.md R8, the
//! `Model` declarations, specifications of std functions, the lemmas of the drafts, and the
//! wrappers that call a callee with its `requires` assumed (`assumed_requires`).

use crate::thrust_models;

pub mod iter;
pub mod assumed_requires;
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
