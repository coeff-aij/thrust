//! Specifications of std functions the case study calls that std.rs does not specify.

use crate::thrust_models;
use thrust_models::model::BitVec;

// The two methods `Niche::available` calls. Each is exact over 128-bit bit-vectors.
#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result == (BitVec::<128, false>::from_int(x) + BitVec::from_int(y)).to_int())]
fn _extern_spec_u128_wrapping_add(x: u128, y: u128) -> u128 {
    u128::wrapping_add(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result == (BitVec::<128, false>::from_int(x) - BitVec::from_int(y)).to_int())]
fn _extern_spec_u128_wrapping_sub(x: u128, y: u128) -> u128 {
    u128::wrapping_sub(x, y)
}
