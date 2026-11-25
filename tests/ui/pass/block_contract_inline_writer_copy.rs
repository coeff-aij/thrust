//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `&mut` variable passed on to a writer inside the body, as a copy operand.
#[thrust_macros::ensures(!x == *x + 1)]
fn writer(x: &mut i64) {
    *x += 1;
}

fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract_inline!(
        |r: &mut i64| -> ()
        requires(*r == 0),
        ensures(!r == 1),
        {
            writer(r);
        }
    );
    *r += 1;
    assert!(a == 2);
}
