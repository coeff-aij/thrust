//@check-pass
//@compile-flags: -C debug-assertions=off
use thrust_models::forall;
// A quantified formula.
fn main() {
    let x = 1_i64;
    thrust_macros::proof_assert!(|x: i64| forall(|k: i64| k == k || k == x));
}
