//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// `retain` keeps a subsequence of the vector, and every element kept is one the closure can
// accept.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!v).len() <= (*v).len()
        && thrust_models::forall(|k: thrust_models::model::Int|
            !(0 <= k && k < (!v).len()) || (!v)[k] > 1)
)]
fn positives(v: &mut Vec<i64>) {
    v.retain(|&x| x > 0);
}

fn main() {}
