//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// The fail twin of `pass/sum_range.rs`: the postcondition claims `n + 1`.
// Creusot's `sum_range` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's code
// and Thrust's annotations: a `for` loop over std's `Range<isize>` through std.rs's
// `IteratorSpec`, concrete. The invariant also states where `iter_old` starts, which Creusot knows
// from the loop's `into_iter`.
use thrust_models::model::{Int, Seq};
use thrust_models::{FnParam, Ghost};

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n + 1)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    for _ in 0..n {
        thrust_macros::invariant!(|iter: core::ops::Range<isize>, iter_old: Ghost<core::ops::Range<isize>>, produced: Ghost<Seq<Int>>, i: isize, n: FnParam<isize>|
            iter_old.start == 0 && iter_old.end == n.at_entry()
                && i == produced.len() && i <= n.at_entry());
        i += 1;
    }
    i
}
