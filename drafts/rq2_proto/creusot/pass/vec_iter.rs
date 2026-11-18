//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `vec_iter` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's code
// and Thrust's annotations: a `for` loop over `&Vec<T>`, which std.rs's `IntoIteratorSpec` turns
// into std's `slice::Iter`, generic in the element type only. The invariant also states where
// `iter_old` starts, which Creusot knows from the loop's `into_iter`.
use thrust_models::model::Seq;
use thrust_models::{FnParam, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(vec.len() < 1000)]
#[thrust_macros::ensures(result == vec.len())]
pub fn vec_iter<T: Model>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    for _ in vec {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, T>, iter_old: Ghost<core::slice::Iter<'_, T>>, produced: Ghost<Seq<&<T as Model>::Ty>>, i: usize, vec: FnParam<&Vec<T>>|
            iter_old.0 == *vec.at_entry() && iter_old.1 == 0 && i == produced.len());
        i += 1;
    }
    i
}
