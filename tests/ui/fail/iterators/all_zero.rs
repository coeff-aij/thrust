//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The loop writes `1`, so the claim that every element ends up zero is false of every
// non-empty vector.
use thrust_models::forall;
use thrust_models::model::Int;

#[thrust_macros::context]
#[thrust_macros::requires((*v).len() >= 0)]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|i: Int| (0 <= i && i < (!v).len()) ==> ((!v)[i] == 0))
)]
fn all_zero(v: &mut Vec<usize>) {
    let mut it = v.iter_mut();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                it.0 == v.at_entry()
                    && it.1 <= (*it.0).len()
                    && forall(|j: Int| (0 <= j && j < it.1) ==> ((!it.0)[j] == 0))
        );
        *x = 1;
    }
}

fn main() {}
