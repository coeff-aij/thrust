//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `map` calls its closure on each item `sum` takes, where its precondition holds; the closure
// is run by std's `sum`, through the `Map` it is handed over in.
#[thrust_macros::requires(thrust_models::forall(|i: thrust_models::model::Int| !(0 <= i && i < (*v).len()) || (*v)[i] < 10))]
#[thrust_macros::ensures(true)]
fn small(v: &[u64]) -> usize {
    v.iter().map(|w| { assert!(*w < 10); 1usize }).sum()
}

fn main() {}
