//@ignore-on-host: not yet verifiable, the solver gives no answer within 300 s: the postcondition unknown of the closure sits under the `forall` of `find`'s contract over the rejected items, as in closure_find_first_unannotated.rs
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As iterator_find.rs, with the closure's contract inferred.
fn main() {
    let v = [1i64, 5, 3];
    if let Some(x) = v.iter().find(|x| **x > 4) {
        assert!(*x == 1);
    }
}
