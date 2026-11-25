//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// `pass/sum_range.rs` with every `invariant!` removed: the loop invariant is left to inference.
// Creusot's `sum_range` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's code
// and Thrust's annotations: a `for` loop over std's `Range<isize>` through std.rs's
// `IteratorSpec`, concrete. The invariant also states where `iter_old` starts, which Creusot knows
// from the loop's `into_iter`.
use thrust_models::model::{Int, Seq};
use thrust_models::{FnParam, Ghost};

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    for _ in 0..n {
        i += 1;
    }
    i
}
