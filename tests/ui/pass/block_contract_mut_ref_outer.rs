//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `mut` `&mut` parameter is passed as in a call: the outer prophecy is kept, so the variable has
// the written value once the reference is dead.
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
    assert!(a == 7);
}
