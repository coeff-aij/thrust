//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `&mut` passed to a call in the block is reborrowed, so what the call ensures of the callee
// holds of the variable afterwards.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!r == 1)]
fn set(r: &mut i64) {
    *r = 1;
}

fn main() {
    let mut x = 0_i64;
    let b = &mut x;
    thrust_macros::block_contract!(
        |mut b: &mut i64| -> ()
        requires(true),
        ensures(!b == 1),
        {
            set(b);
        }
    );
    assert!(x == 1);
}
