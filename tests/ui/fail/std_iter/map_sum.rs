//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// std's `sum` runs the closure `map` holds on every item of the slice, so its precondition must
// hold of each: here nothing bounds the items.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn small(v: &[u64]) -> usize {
    v.iter().map(|w| { assert!(*w < 10); 1usize }).sum()
}

fn main() {}
