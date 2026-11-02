//@check-pass
//@compile-flags: -C debug-assertions=off

// A quantified formula.
fn main() {
    let x = 1_i64;
    thrust_macros::proof_assert!(|x: i64| thrust_models::forall(|k: i64| k == k || k == x));
}
