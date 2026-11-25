//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[thrust_macros::ensures(!x == *x + 1)]
fn writer(x: &mut i64) {
    *x += 1;
}

fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract!(
        |r: &mut i64| -> ()
        requires(*r == 0),
        ensures(!r == 1),
        {
            writer(r);
        }
    );
    *r += 1;
    assert!(a == 3);
}
