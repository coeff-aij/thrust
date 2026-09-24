//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == x && result == 1)]
fn unit_value<T: PartialEq>(x: T) -> i64 {
    0
}

fn main() {
    assert!(unit_value(()) == 0);
}
