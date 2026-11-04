//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The loop writes `1`, so the claim that every element ends up zero is false of every
// non-empty vector.
use thrust_models::forall;
use thrust_models::model::Int;

#[thrust_macros::context]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|i: Int| (0 <= i && i < (!v).len()) ==> ((!v)[i] == 0))
)]
fn all_zero(v: &mut Vec<usize>) {
    for x in v.iter_mut() {
        thrust_macros::invariant!(
            |iter: core::slice::IterMut<'_, usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                iter.0 == *v.at_entry()
                    && iter.1 == !v.at_entry()
                    && iter.1.len() == iter.0.len()
                    && iter.2 <= iter.0.len()
                    && forall(|j: Int| (0 <= j && j < iter.2) ==> (iter.1[j] == 0))
        );
        *x = 1;
    }
}

fn main() {}
