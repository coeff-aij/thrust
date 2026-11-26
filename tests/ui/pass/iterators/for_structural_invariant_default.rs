//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over a range with no invariant written: Thrust conjoins the structural invariant of
// `IteratorSpec` to the inferred one, and the loop is verified.

#[thrust_macros::context]
fn count() -> i64 {
    let mut c = 0;
    for _i in 0..3i64 {
        c += 1;
    }
    assert!(c == 3);
    c
}

fn main() {
    let _ = count();
}
