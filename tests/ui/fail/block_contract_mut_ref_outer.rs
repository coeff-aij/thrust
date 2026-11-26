//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// wrong twin of `pass/block_contract_mut_ref_outer.rs`
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract!(
        |mut r: &mut i64| -> ()
        requires(*r == 0),
        ensures(!r == 7),
        {
            *r = 7;
        }
    );
    assert!(a == 8);
}
