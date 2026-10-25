//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost term reads `x` after a closure that captured it by `&mut` incremented it and was last
// called: the borrow is resolved there, and `x` is `1`, not `0`.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 0)]
#[thrust_macros::ensures(true)]
fn is_zero(g: Ghost<i64>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn captured() {
    let mut x: i64 = 0;
    let mut inc = || x += 1;
    inc();
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    is_zero(g);
}

fn main() {
    captured();
}
