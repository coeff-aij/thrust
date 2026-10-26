//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `for` over std's `Skip`: `skip(1)` drops the first item of a non-empty vector.
// Fail twin: it drops only one.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(v.len() == 0 || result + 1 < v.len())]
fn count_after_first(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for _x in v.iter().skip(1) {
        thrust_macros::invariant!(|iter: core::iter::Skip<core::slice::Iter<'_, i64>>, iter_old: Ghost<core::iter::Skip<core::slice::Iter<'_, i64>>>, produced: Ghost<Seq<&Int>>, c: usize, v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 .0 == *v.at_entry() && iter_old.0 .1 == 0 && iter_old.1 == 1 && c == produced.len());
        c += 1;
    }
    c
}

fn main() {}
