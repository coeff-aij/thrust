//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost term reads a variable after its last use: in the same block, and after a call, which
// ends the block. Its value is the one the variable had at its last use; after the call that is
// `6`, not the `5` `is_five` requires.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 5)]
#[thrust_macros::ensures(true)]
fn is_five(g: Ghost<i64>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(x == 5)]
#[thrust_macros::ensures(true)]
fn same_block(x: i64) {
    let y = x + 1;
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    is_five(g);
}

#[thrust_macros::requires(x == 6)]
#[thrust_macros::ensures(true)]
fn across_call(x: i64) {
    let y = id(x);
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    is_five(g);
}

fn main() {
    same_block(5);
    across_call(6);
}
