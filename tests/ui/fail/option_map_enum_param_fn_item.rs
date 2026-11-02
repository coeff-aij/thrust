//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A function item taking an `Option<i64>` that it writes through, passed to `Option::map`: the
// precondition the call requires includes the refinement of the argument's payload.
fn h(o: Option<i64>) -> i64 {
    let mut o = o;
    if let Some(x) = &mut o {
        *x += 1;
    }
    0
}

fn main() {
    let r = Some(Some(3i64)).map(h);
    assert!(r == Some(1));
}
