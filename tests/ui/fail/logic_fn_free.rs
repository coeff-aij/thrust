//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:07c15d715

#[thrust_macros::logic]
fn double(x: i64) -> i64 {
    x * 2
}

#[thrust_macros::logic]
fn quad(x: i64) -> i64 {
    double(double(x))
}

#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result == double(x) + 1 && quad(x) == 2 * double(x))]
fn double_plus_one(x: i64) -> i64 {
    x + x + 2
}

fn main() {
    assert!(double_plus_one(3) == 7);
}
