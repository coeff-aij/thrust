//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `old!(x)` in a `proof_assert!` is the parameter's value on entry, which `x` no longer holds.
fn h(mut x: i64) {
    x += 1;
    thrust_macros::proof_assert!(|x: i64, old!(x): i64| x == old!(x));
}

fn main() {
    h(1);
}
