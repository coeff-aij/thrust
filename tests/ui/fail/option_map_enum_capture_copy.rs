//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A closure that copies the `Option<i64>` it captures into a mutable local and writes through
// it: the body assumes the refinement of the captured payload, which `Option::map`'s
// precondition requires.
fn main() {
    let o = Some(0i64);
    let c = move |v: i64| -> i64 {
        let mut o = o;
        if let Some(x) = &mut o {
            *x += v;
        }
        0
    };
    let r = Some(5i64).map(c);
    assert!(r == Some(1));
}
