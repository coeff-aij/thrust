//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `for` over std's `Cloned`: each item is the element the inner iterator refers to. `Copied`
// has the same contract.
// Fail twin: the elements are only known to be positive.

use thrust_models::model::{Int, Seq};
use thrust_models::{forall, Ghost};

#[thrust_macros::context]
#[thrust_macros::requires(forall(|i: Int| !(0 <= i && i < v.len()) || v[i] > 0))]
#[thrust_macros::ensures(true)]
fn all_pos_cloned(v: &Vec<i64>) {
    for x in v.iter().cloned() {
        thrust_macros::invariant!(|iter: core::iter::Cloned<core::slice::Iter<'_, i64>>, iter_old: Ghost<core::iter::Cloned<core::slice::Iter<'_, i64>>>, produced: Ghost<Seq<Int>>, v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 == *v.at_entry() && iter_old.1 == 0
                && forall(|i: Int| !(0 <= i && i < iter_old.0.len()) || iter_old.0[i] > 0));
        assert!(x > 1);
    }
}

fn main() {}
