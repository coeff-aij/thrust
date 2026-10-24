//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost term reads a variable whose value was moved out: it reads the value before the move, as
// a Creusot snapshot does. Here that is `6`, not the `5` `is_five` requires.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 5)]
#[thrust_macros::ensures(true)]
fn is_five(g: Ghost<i64>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn consume(v: Box<i64>) {}

#[thrust_macros::requires(*v == 6)]
#[thrust_macros::ensures(true)]
fn moved(v: Box<i64>) {
    consume(v);
    let g = thrust_macros::ghost!(|v: Box<i64>| -> i64 { *v });
    is_five(g);
}

fn main() {
    moved(Box::new(6));
}
