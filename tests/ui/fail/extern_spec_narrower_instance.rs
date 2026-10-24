//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The body of `get` breaks the spec at the instance a call reaches, so the call is not verified:
// the spec, which covers only the instances whose projection `R::Output` is `usize`, is checked
// against the body at that instance.
use std::slice::SliceIndex;

pub trait IntoIdx {
    type Output: SliceIndex<[u64]>;

    fn into_idx(self) -> Self::Output;
}

impl IntoIdx for usize {
    type Output = usize;

    fn into_idx(self) -> usize {
        self / 2
    }
}

fn get<R: IntoIdx>(v: &[u64], r: R) -> &<R::Output as SliceIndex<[u64]>>::Output {
    &v[r.into_idx()]
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(r < (*v).len())]
#[thrust_macros::ensures(*result == (*v)[r])]
fn _extern_spec_get(v: &[u64], r: usize) -> &u64 {
    get(v, r)
}

#[thrust_macros::requires((*v).len() == 3 && (*v)[1] == 2)]
#[thrust_macros::ensures(true)]
fn check(v: &[u64]) {
    let x = get(v, 1usize);
    assert!(*x == 2);
}

fn main() {}
