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
    let w = v;
    for i in 0..w.len() {
        thrust_macros::invariant!(
            |iter: core::ops::Range<usize>, w: &mut Vec<usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                iter.start <= iter.end
                    && iter.end == (*v.at_entry()).len()
                    && (*w).len() == (*v.at_entry()).len()
                    && !w == !v.at_entry()
                    && forall(|j: Int| (0 <= j && j < iter.start) ==> ((*w)[j] == 0))
        );
        w[i] = 1;
    }
}
