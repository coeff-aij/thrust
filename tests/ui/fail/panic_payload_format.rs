//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `panic!` with a formatted message reaches `core::panicking::panic_fmt`.
fn main() {
    let x: u64 = 5;
    if x > 3 {
        panic!("x is {x}, above 3");
    }
}
