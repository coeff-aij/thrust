//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

#[thrust_macros::logic]
fn count(x: i64) -> i64 {
    count(x - 1) + 1 //~ ERROR: a logic function cannot call itself
}

#[thrust_macros::ensures(result == count(x))]
fn f(x: i64) -> i64 {
    x
}

fn main() {
    f(0);
}
