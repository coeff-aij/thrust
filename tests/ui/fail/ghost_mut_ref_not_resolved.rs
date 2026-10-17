//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost of a `&mut` is a snapshot: its death does not resolve the borrow, which the function
// still writes through.
// Fail twin: the value the borrow had when the ghost was taken.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!x == *x)]
fn bump(x: &mut i64) {
    let _g = thrust_macros::ghost!(|x: &mut i64| -> &mut i64 { x });
    *x += 1;
}

fn main() {
    let mut a = 0;
    bump(&mut a);
    assert!(a == 1);
}
