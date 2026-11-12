//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The loop writes `1`, so the claim that every element ends up zero is false of every
// non-empty vector.
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
        *x = 1;
    }
}
