//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `retain` asks the closure's precondition of every element of the vector.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!v).len() <= (*v).len()
        && thrust_models::forall(|k: thrust_models::model::Int|
            !(0 <= k && k < (!v).len()) || (!v)[k] > 0)
)]
fn positives(v: &mut Vec<i64>) {
    v.retain(thrust_macros::closure!(requires(*x > 0), ensures(result == (*x > 0)), |x: &i64| -> bool { *x > 0 }));
}

fn main() {}
