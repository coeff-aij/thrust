//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at `char` ranges over the Unicode scalar values, also without
// `THRUST_INT_RANGE`, so assuming a statement true of every `char` assumes nothing false.
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0 && forall(|c: char| c <= char::MAX));
    assert!(x == 0);
}
