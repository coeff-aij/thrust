//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `for` over std's `Skip` and `Take`: the count of items is bounded by what each adapter lets
// through.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= v.len())]
fn count_pos_after_first(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for x in v.iter().skip(1) {
        thrust_macros::invariant!(|iter: core::iter::Skip<core::slice::Iter<'_, i64>>, iter_old: Ghost<core::iter::Skip<core::slice::Iter<'_, i64>>>, produced: Ghost<Seq<&Int>>, c: usize, v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 .0 == *v.at_entry() && iter_old.0 .1 == 0 && iter_old.1 == 1 && c <= produced.len());
        if *x > 0 {
            c += 1;
        }
    }
    c
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 3)]
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
