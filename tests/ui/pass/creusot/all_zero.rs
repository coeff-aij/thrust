//@check-pass
//@compile-flags: --crate-type=lib -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Creusot's `all_zero`: every element of the vector is set to zero by a `for` loop over
// `iter_mut`. The loop's iterator `iter` holds the vector's entry and final sequences, so the
// invariant quantifies over the positions already passed and the postcondition over all of them;
// `slice::IterMut` has no `IteratorSpec`, so the invariant names `iter` and not `produced`.
use thrust_models::forall;
use thrust_models::model::Int;

#[thrust_macros::context]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|i: Int| (0 <= i && i < (!v).len()) ==> ((!v)[i] == 0))
)]
pub fn all_zero(v: &mut Vec<usize>) {
    for x in v.iter_mut() {
        thrust_macros::invariant!(
            |iter: core::slice::IterMut<'_, usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                iter.0 == *v.at_entry()
                    && iter.1 == !v.at_entry()
                    && iter.1.len() == iter.0.len()
                    && iter.2 <= iter.0.len()
                    && forall(|j: Int| (0 <= j && j < iter.2) ==> (iter.1[j] == 0))
        );
        *x = 0;
    }
}
