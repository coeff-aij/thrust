//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(a <= b)]
#[thrust_macros::ensures(a + result == b + 1)]
fn gap(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

fn main() {
    assert!(7u8.abs_diff(10) == 3);
}
