//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `&mut` parameter not written `mut` is not written through: its value is kept after the block.
fn main() {
    let mut a = 3i64;
    let r = &mut a;
    let v = thrust_macros::block_contract!(
        |r: &mut i64| -> i64
        requires(true),
        ensures(result == *r),
        {
            *r
        }
    );
    assert!(*r == 3 && v == 3);
}
