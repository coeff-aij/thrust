//@error-in-other-file: both cover some of its instances
//@compile-flags: -C debug-assertions=off

// A generic extern spec of `cmp::max` is the contract of its calls. A second spec of
// `cmp::max` at `u64` would cover instances the first covers too, and is rejected
// (`fail/extern_spec_overlap_generic.rs`): an instance takes at most one extern spec.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(v1 != v2)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max<T: Ord + thrust_models::Model>(v1: T, v2: T) -> T {
    std::cmp::max(v1, v2)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max_word(v1: u64, v2: u64) -> u64 {
    std::cmp::max(v1, v2)
}

fn main() {
    let m = std::cmp::max(3u64, 4);
    assert!(m == 3 || m == 4);
}
