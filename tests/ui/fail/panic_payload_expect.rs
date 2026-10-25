//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Option::expect` on `None` panics.
fn main() {
    let o: Option<u32> = None;
    let _ = o.expect("o is some");
}
