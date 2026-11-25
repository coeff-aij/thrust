//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over `v.iter_mut()` whose invariant names the iterator `iter` alone: `slice::IterMut`
// has no `IteratorSpec`, so the loop is desugared without `iter_old` and `produced`.
use thrust_models::{forall, model::Int};
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|k: Int|
    !(0 <= k && k < result.len()) || result[k] == 0))]
fn clear(mut v: Vec<i64>) -> Vec<i64> {
    for x in v.iter_mut() {
        thrust_macros::invariant!(|iter: core::slice::IterMut<'_, i64>, v: Vec<i64>|
            v == iter.1
                && iter.0.len() == iter.1.len()
                && 0 <= iter.2 && iter.2 <= iter.0.len()
                && forall(|k: Int|
                    !(0 <= k && k < iter.2) || iter.1[k] == 0));
        *x = 0;
    }
    v
}

fn main() {}
