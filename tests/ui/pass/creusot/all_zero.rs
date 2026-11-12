//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Creusot's `all_zero`: every element of the vector is set to zero by a `for` loop over
// `iter_mut`. As in Creusot, the invariant states that every item produced so far ends up zero;
// the loop's history (`inv(iter)` and `produces(iter_old, produced, iter)`) is conjoined to it.
// The closure names `iter` with its type, which the history's ghosts take theirs from.
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|i: Int| (0 <= i && i < (!v).len()) ==> ((!v)[i] == 0))
)]
fn all_zero(v: &mut Vec<usize>) {
    for x in v.iter_mut() {
        thrust_macros::invariant!(
            |iter: core::slice::IterMut<'_, usize>, produced: Ghost<Seq<<&mut usize as Model>::Ty>>|
                forall(|i: Int| (0 <= i && i < produced.len()) ==> (!produced[i] == 0))
        );
        *x = 0;
    }
}
