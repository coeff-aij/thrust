//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `for` over std's `Take`: it hands out at most `n` items.
// Fail twin: `take(3)` can hand out three items.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result < 3)]
fn count_first_three(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for _x in v.iter().take(3) {
        thrust_macros::invariant!(|iter: core::iter::Take<core::slice::Iter<'_, i64>>, iter_old: Ghost<core::iter::Take<core::slice::Iter<'_, i64>>>, produced: Ghost<Seq<&Int>>, c: usize, v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 .0 == *v.at_entry() && iter_old.0 .1 == 0 && iter_old.1 == 3 && c == produced.len());
        c += 1;
    }
    c
}

fn main() {}
