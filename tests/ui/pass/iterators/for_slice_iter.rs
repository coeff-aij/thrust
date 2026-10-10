//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over `v.iter()` whose invariant bounds a count by the number of items produced.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= v.len())]
fn count_pos(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for x in v.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>, iter_old: Ghost<core::slice::Iter<'_, i64>>, produced: Ghost<Seq<Int>>, c: usize, v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 == *v.at_entry() && iter_old.1 == 0 && c <= produced.len());
        if *x > 0 {
            c += 1;
        }
    }
    c
}

fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(-2);
    assert!(count_pos(&v) <= 2);
}
