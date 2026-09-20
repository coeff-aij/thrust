//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Creusot's `all_zero`: every element of the vector is set to zero through `iter_mut`. The
// iterator's first component is the vector's prophecy pair, so the invariant quantifies over the
// positions already passed and the postcondition over all of them.
use thrust_models::forall;
use thrust_models::model::Int;

#[thrust_macros::context]
#[thrust_macros::requires((*v).length >= 0)]
#[thrust_macros::ensures(
    (!v).length == (*v).length
        && forall(|i: Int| (0 <= i && i < (!v).length) ==> ((!v).array[i] == 0))
)]
fn all_zero(v: &mut Vec<usize>) {
    let mut it = v.iter_mut();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                it.0 == v.at_entry()
                    && it.1 <= (*it.0).length
                    && forall(|j: Int| (0 <= j && j < it.1) ==> ((!it.0).array[j] == 0))
        );
        *x = 0;
    }
}

fn main() {}
