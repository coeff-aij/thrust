//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `get` breaks its narrower extern spec (`into_idx` halves), reached through a function pointer
// to `get::<usize>`: the body is checked at that instance.
use std::slice::SliceIndex;
pub trait IntoIdx {
    type Output: SliceIndex<[u64]>;
    fn into_idx(self) -> Self::Output;
}
impl IntoIdx for usize {
    type Output = usize;
    fn into_idx(self) -> usize { self / 2 }
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
#[thrust_macros::requires((*v).len() == 3 && (*v)[1] == 2 && (*v)[0] == 0)]
#[thrust_macros::ensures(true)]
fn check(v: &[u64]) {
    let f: for<'a> fn(&'a [u64], usize) -> &'a u64 = get::<usize>;
    let x = f(v, 1usize);
    assert!(*x == 2);
}
fn main() {}
