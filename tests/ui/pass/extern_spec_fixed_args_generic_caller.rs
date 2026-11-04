//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of `cmp::max` at `u64` does not cover the call in `larger` at its type
// parameter, which takes the generic spec.

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

#[thrust_macros::requires(a != b)]
#[thrust_macros::ensures(result == a || result == b)]
fn larger<T: Ord + thrust_models::Model>(a: T, b: T) -> T {
    std::cmp::max(a, b)
}

fn main() {
    let m = larger(3u64, 4);
    assert!(m == 3 || m == 4);
}
