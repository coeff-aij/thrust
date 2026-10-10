//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin writing 1.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_models::forall(|k: thrust_models::model::Int|
    !(0 <= k && k < result.len()) || result[k] == 0))]
fn clear(mut v: Vec<i64>) -> Vec<i64> {
    for x in v.iter_mut() {
        thrust_macros::invariant!(|iter: core::slice::IterMut<'_, i64>, v: Vec<i64>|
            v == iter.1
                && iter.0.len() == iter.1.len()
                && 0 <= iter.2 && iter.2 <= iter.0.len()
                && thrust_models::forall(|k: thrust_models::model::Int|
                    !(0 <= k && k < iter.2) || iter.1[k] == 0));
        *x = 1;
    }
    v
}

fn main() {}
