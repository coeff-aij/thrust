//@ignore-on-host: not yet verifiable, the solver gives no answer within 300 s: the postcondition unknown of the closure sits under the `forall` of `all`'s contract over the accepted items, as in iterator_find_unannotated.rs
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As iterator_all.rs, with the closure's contract inferred.
fn main() {
    let v = [1i64, 5, 3];
    let b = v.iter().all(|x| *x > 0);
    assert!(!b);
}
