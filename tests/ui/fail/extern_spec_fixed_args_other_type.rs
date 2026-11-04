//@error-in-other-file: no specification
//@compile-flags: -C debug-assertions=off

// An extern spec of `cmp::max` at `u64` is the contract of the calls at `u64` and says
// nothing of a call at `i64`, whose type has the same sort: that call has no specification.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max_word(v1: u64, v2: u64) -> u64 {
    std::cmp::max(v1, v2)
}

fn main() {
    let m = std::cmp::max(3i64, 4);
    assert!(m == 3 || m == 4);
}
