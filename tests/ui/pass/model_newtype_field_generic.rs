//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:0360cb142

// A struct that declares the model of its only non-zero-sized field is that field in the logic
// also in a function that leaves the element type unbounded: the value is a sequence, not the
// `(sequence, unit)` tuple of the struct's fields, so `len` on it is a sequence operation.

use std::marker::PhantomData;

struct IndexVec<I, T> {
    raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I, T: thrust_models::Model> thrust_models::Model for IndexVec<I, T> {
    type Ty = <Vec<T> as thrust_models::Model>::Ty;
}

struct IndexSlice<I, T> {
    _marker: PhantomData<fn(&I)>,
    raw: [T],
}

impl<I, T: thrust_models::Model> thrust_models::Model for IndexSlice<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
impl<I, T> IndexVec<I, T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).len())]
    fn len(&self) -> usize {
        self.raw.len()
    }
}

#[thrust_macros::context]
impl<I, T> IndexSlice<I, T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).len())]
    fn len(&self) -> usize {
        self.raw.len()
    }
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == (*v).len())]
fn vec_len<I, T>(v: &IndexVec<I, T>) -> usize {
    v.len()
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == (*s).len())]
fn slice_len<I, T>(s: &IndexSlice<I, T>) -> usize {
    s.len()
}

fn main() {}
