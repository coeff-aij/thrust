//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `skip_take` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's code
// and Thrust's annotations: `iter.take(n).skip(n).next()` is `None` for any iterator, over std's
// `take` and `skip` with std.rs's specifications, as Creusot's uses creusot-std's.
// `requires(I::inv(iter))` is Creusot's type invariant of `iter`.
use thrust_models::Model;

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter))]
pub fn skip_take<I: IteratorSpec>(iter: I, n: usize)
where
    I::Item: Model,
{
    let res = iter.take(n).skip(n).next();

    thrust_macros::proof_assert!(|res: Option<I::Item>| res == None);
}
