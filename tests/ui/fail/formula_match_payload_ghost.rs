//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `match` in a ghost update is a value: it pushes an `Option`'s payload onto a ghost sequence
// without an executable branch.
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::requires(s.len() == 1 && s[0] == x)]
#[thrust_macros::ensures(true)]
fn expect_one(s: Ghost<Seq<Int>>, x: i64) {}

#[thrust_macros::requires(s.len() == 0)]
#[thrust_macros::ensures(true)]
fn expect_empty(s: Ghost<Seq<Int>>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn push_some(x: i64) {
    let r = Some(x);
    let empty = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    let pushed = thrust_macros::ghost!(|empty: Ghost<Seq<Int>>, r: Option<i64>| -> Seq<Int> {
        match r {
            Some(x) => empty.push(x + 1),
            None => empty,
        }
    });
    expect_one(pushed, x);
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn push_none() {
    let r: Option<i64> = None;
    let empty = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    let pushed = thrust_macros::ghost!(|empty: Ghost<Seq<Int>>, r: Option<i64>| -> Seq<Int> {
        match r {
            Some(x) => empty.push(x),
            None => empty,
        }
    });
    expect_empty(pushed);
}

fn main() {
    push_some(7);
    push_none();
}
