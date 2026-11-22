//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A predicate a trusted `ensures` calls is read over Rust values there, through its own instance:
// its variable at an unsigned type ranges over the values of the type.
use thrust_models::forall;

#[thrust_macros::predicate]
fn below_all(r: u64) -> bool {
    forall(|n: u64| r <= n)
}

#[thrust::trusted]
#[thrust_macros::ensures(below_all(result))]
fn least() -> u64 {
    0
}

fn main() {
    let r = least();
    assert!(r == 1);
}
