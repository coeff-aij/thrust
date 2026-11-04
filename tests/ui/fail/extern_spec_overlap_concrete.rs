//@compile-flags: -C debug-assertions=off

// An extern spec of `u64::is_power_of_two`, a function without type parameters, covers its one
// instance. A second spec of it is rejected (`fail/extern_spec_overlap_concrete.rs`), as is a
// crate's spec of a function std.rs specifies.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == 0 ==> !result)]
fn _extern_spec_is_power_of_two(x: u64) -> bool {
    u64::is_power_of_two(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == 1 ==> result)]
fn _extern_spec_is_power_of_two_one(x: u64) -> bool { //~ ERROR: already has a contract
    u64::is_power_of_two(x)
}

fn main() {
    assert!(!0u64.is_power_of_two());
}
