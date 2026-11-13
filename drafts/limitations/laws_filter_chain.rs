// std.rs compiled as a source file with `#[thrust::trusted]` removed from the `produces_trans` of
// `Filter` and `Chain`; `std_untrusted.rs` is made from std.rs by the command in README.md.
// Run with `THRUST_NO_INJECT_STD=1` and `THRUST_VERIFY_ONLY` naming one of the two laws.
#![feature(specialization)]
#![allow(incomplete_features)]

include!("std_untrusted.rs");

fn main() {}
