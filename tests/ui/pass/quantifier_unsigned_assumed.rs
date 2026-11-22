//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable an `assume!` binds at an unsigned type ranges over the values of the type, also
// without THRUST_INT_RANGE: the assumption is true of Rust values, so it assumes nothing false.
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0 && forall(|n: u64| n >= 0));
    assert!(x == 0);
}
