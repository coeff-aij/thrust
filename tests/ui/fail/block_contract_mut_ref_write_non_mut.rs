//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `&mut` parameter not written `mut` is written through: the check of the body fails.
// The twin is `pass/block_contract_mut_ref.rs`, where the parameter is `mut`.
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract!(
        |r: &mut i64| -> ()
        requires(*r == 0),
        ensures(true),
        {
            *r = 1;
        }
    );
    *r += 1;
}
