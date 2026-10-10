//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `for_range_sum` with a `partial_invariant!`: the written part gives the sum over `produced`, and
// inference adds what the full form restates (the bounds of `iter_old`).

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum(n: i64) -> i64 {
    let mut s = 0;
    for i in 0..n {
        thrust_macros::partial_invariant!(|iter: core::ops::Range<i64>, iter_old: Ghost<core::ops::Range<i64>>, produced: Ghost<Seq<Int>>, s: i64|
            2 * s == produced.len() * (produced.len() - 1));
        s += i;
    }
    s
}

fn main() {
    assert!(sum(4) == 6);
}
