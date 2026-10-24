//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost local updated in a loop from its own value: the ghost term that reads it is its only
// use, which keeps it a parameter of the loop head. It counts the iterations, not one more.
use thrust_models::model::Int;
use thrust_models::Ghost;

#[thrust_macros::requires(g == n)]
#[thrust_macros::ensures(true)]
fn equals(g: Ghost<Int>, n: i64) {}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(true)]
fn count(n: i64) {
    let mut g = thrust_macros::ghost!(|| -> Int { 0 });
    let mut i = 0;
    while i < n {
        g = thrust_macros::ghost!(|g: Ghost<Int>| -> Int { g + 1 });
        i += 1;
    }
    equals(g, n + 1);
}

fn main() {
    count(3);
}
