//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `slice_iter` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's code
// and Thrust's annotations: a `for` loop over std's `slice::Iter` through std.rs's `IteratorSpec`,
// generic in the element type only. The invariant also states where `iter_old` starts, which
// Creusot knows from the loop's `into_iter`.
use thrust_models::model::Seq;
use thrust_models::{FnParam, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(slice.len() < 1000)]
#[thrust_macros::ensures(result == slice.len())]
pub fn slice_iter<T: Model>(slice: &[T]) -> usize {
    let mut i = 0;
    for _ in slice.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, T>, iter_old: Ghost<core::slice::Iter<'_, T>>, produced: Ghost<Seq<&<T as Model>::Ty>>, i: usize, slice: FnParam<&[T]>|
            iter_old.0 == *slice.at_entry() && iter_old.1 == 0 && i == produced.len());
        i += 1;
    }
    i
}
