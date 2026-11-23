//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable of an enum type that the formula reads only through some payload fields is guarded by
// the facts of those fields only: the assumption still holds of every Rust value and assumes
// nothing false.
use thrust_models::forall;

enum E {
    A(u64, u64),
    B(u64),
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|e: E| match e { E::A(a, _) => a >= 0, E::B(_) => true }));
    assert!(x == 1);
}
