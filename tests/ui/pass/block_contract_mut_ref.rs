//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `mut` `&mut` variable of the block is written through in the body as written.
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract!(
        |mut r: &mut i64| -> ()
        requires(*r == 0),
        ensures(!r == 1),
        {
            *r += 1;
        }
    );
    *r += 1;
    assert!(a == 2);
}
