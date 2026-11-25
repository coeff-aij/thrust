//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `vec_len` returns one more than the length its postcondition states, on a value whose element
// type is unbounded.
use thrust_models::Model;
use std::marker::PhantomData;

struct IndexVec<I, T> {
    raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I, T: Model> Model for IndexVec<I, T> {
    type Ty = <Vec<T> as Model>::Ty;
}

struct IndexSlice<I, T> {
    _marker: PhantomData<fn(&I)>,
    raw: [T],
}

impl<I, T: Model> Model for IndexSlice<I, T> {
    type Ty = <[T] as Model>::Ty;
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
    v.len() + 1
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == (*s).len())]
fn slice_len<I, T>(s: &IndexSlice<I, T>) -> usize {
    s.len()
}

fn main() {}
