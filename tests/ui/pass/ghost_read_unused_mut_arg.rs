//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `&mut` argument the program never uses, read only by a ghost term after a call: it is still
// resolved at entry, as before the ghost read, and carried to the read as a block parameter, so
// its final value is the current `5`.
use thrust_models::Ghost;

#[thrust_macros::requires(g == n)]
#[thrust_macros::ensures(true)]
fn is(g: Ghost<i64>, n: i64) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(*r == 5)]
#[thrust_macros::ensures(!r == 5)]
fn unused(r: &mut i64) {
    let z = id(0);
    let g = thrust_macros::ghost!(|r: &mut i64| -> i64 { !r });
    is(g, 5);
}

fn main() {
    let mut a = 5;
    unused(&mut a);
}
