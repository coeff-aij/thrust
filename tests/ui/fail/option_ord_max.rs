//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin taking `None` for the maximum.

fn main() {
    let a: Option<u64> = Some(3);
    let b: Option<u64> = None;
    assert!(a.max(b) == None);
}
