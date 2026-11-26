//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `retain` keeps a subsequence of the vector, and every element kept is one the closure can
// accept.
use thrust_models::{forall, model::Int};
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!v).len() <= (*v).len()
        && forall(|k: Int|
            !(0 <= k && k < (!v).len()) || (!v)[k] > 0)
)]
fn positives(v: &mut Vec<i64>) {
    v.retain(thrust_macros::closure!(ensures(result == (*x > 0)), |x: &i64| -> bool { *x > 0 }));
}

fn main() {}
