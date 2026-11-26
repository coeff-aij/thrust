//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::{forall, model::{Closure, UInt}};
// A trusted function requires an `FnMut` closure's `pre!` at every state and calls it twice; the
// closure fails on its second call. `pre!` of a state holds whatever final state the call ends in,
// so the closure's precondition cannot be that the call leaves its state unchanged.
#[thrust::trusted]
#[thrust_macros::requires(forall(|c: Closure<F>, x: UInt| thrust_macros::pre!(c(x))))]
#[thrust_macros::ensures(true)]
fn twice<F: FnMut(u64) -> u64>(mut f: F) { f(1); f(1); }
fn main() {
    let mut n = 0u64;
    twice(|_x: u64| { n += 1; assert!(n <= 1); 0 });
}
