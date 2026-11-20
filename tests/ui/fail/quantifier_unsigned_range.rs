//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at an unsigned type ranges over the integers `>= 0`, also
// without `THRUST_INT_RANGE`, so assuming a statement true of every `u64` assumes nothing false.
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0 && forall(|n: u64| n >= 0));
    assert!(x == 1);
}
