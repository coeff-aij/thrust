//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:07c15d715

#[thrust_macros::logic]
fn swap(x: i64, y: i64) -> (i64, i64) {
    (y, x)
}

#[thrust_macros::ensures(result == swap(y, x))]
fn keep(x: i64, y: i64) -> (i64, i64) {
    (x, y)
}

fn main() {
    let (a, b) = keep(1, 2);
    assert!(a == 1 && b == 2);
}
