//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `no_structural_invariant!()` at the start of a `for` body leaves out the `inv(iter)` and
// `produces(iter_old, produced, iter)` that Thrust conjoins to the loop's inferred invariant by
// default. The loop is still checked against what is written and what Thrust infers
// (`for_structural_invariant_default.rs` is the same loop without the marker).

#[thrust_macros::context]
fn count() -> i64 {
    let mut c = 0;
    for _i in 0..3i64 {
        thrust_macros::no_structural_invariant!();
        c += 1;
    }
    assert!(c == 4);
    c
}

fn main() {
    let _ = count();
}
