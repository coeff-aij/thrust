//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of `cmp::max` at `u64` covers the call at `u64` in the generic `larger`, and
// not a call at its type parameter, which has no specification.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max_word(v1: u64, v2: u64) -> u64 {
    std::cmp::max(v1, v2)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == a || result == b)]
fn larger<T: Ord + thrust_models::Model>(a: u64, b: u64, c: T, d: T) -> u64 {
    let _ = std::cmp::max(c, d); //~ ERROR: no specification
    std::cmp::max(a, b)
}

fn main() {
    let m = larger(3, 4, 0i32, 1i32);
    assert!(m == 3 || m == 4);
}
