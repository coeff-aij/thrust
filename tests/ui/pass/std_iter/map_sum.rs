//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `map` calls its closure on each item `sum` takes, where its precondition holds; the closure
// is run by std's `sum`, through the `Map` it is handed over in. The closure's contract is
// written, so that its precondition is the one the `requires` of `map` states.
#[thrust_macros::requires(thrust_models::forall(|i: thrust_models::model::Int| !(0 <= i && i < (*v).len()) || (*v)[i] < 10))]
#[thrust_macros::ensures(true)]
fn small(v: &[u64]) -> usize {
    let f = thrust_macros::closure!(
        requires(*w < 10),
        ensures(result == 1),
        |w: &u64| -> usize { 1usize }
    );
    v.iter().map(f).sum()
}

fn main() {}
