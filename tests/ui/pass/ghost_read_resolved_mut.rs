//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost term reads a `&mut` after its last use and a call: the borrow was resolved at its last
// use, so its final value is the current value written then, and the lender holds it right after;
// the ghost read neither delays nor changes the resolution.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 5)]
#[thrust_macros::ensures(true)]
fn is_five(g: Ghost<i64>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn resolved() -> i64 {
    let mut a: i64 = 0;
    let r = &mut a;
    *r = 5;
    let z = id(0);
    let g = thrust_macros::ghost!(|r: &mut i64| -> i64 { !r });
    is_five(g);
    a
}

fn main() {
    resolved();
}
