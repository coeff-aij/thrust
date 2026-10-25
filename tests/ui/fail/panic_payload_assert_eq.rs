//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `assert_eq!` with a message on unequal values reaches `core::panicking::assert_failed`.
fn main() {
    let x: u64 = 1;
    assert_eq!(x + 1, 3, "x is {}", x);
}
