//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `assert_ne!` on equal values reaches `core::panicking::assert_failed`.
fn main() {
    let x: u64 = 2;
    assert_ne!(x, 2);
}
