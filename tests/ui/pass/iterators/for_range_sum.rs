//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over a range whose written invariant names the ghost `produced`, the items `next`
// returned so far, and `iter_old`, the range before the loop. `#[thrust_macros::context]` desugars
// the loop and conjoins `produces(iter_old, produced, iter)` to the invariant.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum(n: i64) -> i64 {
    let mut s = 0;
    for i in 0..n {
        thrust_macros::invariant!(|iter: core::ops::Range<i64>, iter_old: Ghost<core::ops::Range<i64>>, produced: Ghost<Seq<Int>>, s: i64, n: thrust_models::FnParam<i64>|
            0 <= n.at_entry() && iter_old.start == 0 && iter_old.end == n.at_entry()
                && 2 * s == produced.len() * (produced.len() - 1));
        s += i;
    }
    s
}

fn main() {
    assert!(sum(4) == 6);
}
