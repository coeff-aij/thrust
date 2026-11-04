//@compile-flags: -C debug-assertions=off
// A type's const arguments are part of it: a 64-bit vector is not a 32-bit one.

use thrust_models::model::BitVec;

#[thrust_macros::requires(thrust_macros::pre!(g(b)))] //~ ERROR: `pre!` passes a value of type `thrust_models::model::BitVec<64, true>` where the callee takes `thrust_models::model::BitVec<32, true>`
#[thrust_macros::ensures(true)]
fn apply<G: Fn(BitVec<32, true>)>(g: G, b: BitVec<64, true>) {}

fn main() {}
