//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `enumerate_range` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's
// code and Thrust's annotations: a `for` loop over std's `Enumerate<Range<usize>>` through
// std.rs's `IteratorSpec`, concrete. The range is `usize`, as Creusot's invariant makes it by
// comparing the item with its index. The invariant also states where `iter_old` starts, which
// Creusot knows from the loop's `into_iter`. The function has no postcondition, so the invariant
// is the only claim.
use thrust_models::forall;
use thrust_models::model::{Int, Seq, UInt};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
pub fn enumerate_range() {
    for (ix, x) in (0..10).enumerate() {
        thrust_macros::invariant!(|iter: core::iter::Enumerate<core::ops::Range<usize>>, iter_old: Ghost<core::iter::Enumerate<core::ops::Range<usize>>>, produced: Ghost<Seq<(UInt, UInt)>>|
            iter_old.0.start == 0 && iter_old.0.end == 10 && iter_old.1 == 0
                && forall(|i: Int| 0 <= i && i < produced.len() ==> produced[i].0 == produced[i].1));
        let _ = (ix, x);
    }
}
