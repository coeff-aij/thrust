//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// An extern spec of `cmp::max` at `u64` is the contract of the calls at `u64`, in place of the
// generic spec, which it must refine there: its precondition may be weaker, not stronger.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(v1 != v2)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max<T: Ord + thrust_models::Model>(v1: T, v2: T) -> T {
    std::cmp::max(v1, v2)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(v1 != 5)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max_word(v1: u64, v2: u64) -> u64 {
    std::cmp::max(v1, v2)
}

fn main() {
    let m = std::cmp::max(3u64, 3);
    assert!(m == 3);
}
