//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::Model;
use std::ops::Index;
use std::slice::SliceIndex;

trait Key<T> {
    type Output: SliceIndex<[T]>;

    fn key(self) -> Self::Output;
}

impl<T> Key<T> for usize {
    type Output = usize;

    fn key(self) -> usize {
        self
    }
}

struct Seq<T> {
    raw: Vec<T>,
}

impl<T: Model> Model for Seq<T> {
    type Ty = <Vec<T> as Model>::Ty;
}

impl<T, R: Key<T>> Index<R> for Seq<T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    #[thrust::trusted]
    fn index(&self, index: R) -> &Self::Output {
        &self.raw[index.key()]
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == 5)]
fn _extern_spec_seq_index<R: Key<i64, Output = usize> + Model>(
    s: &Seq<i64>,
    index: R,
) -> &i64 {
    <Seq<i64> as Index<R>>::index(s, index)
}

fn main() {
    let s: Seq<i64> = Seq { raw: Vec::new() };
    assert!(s[0_usize] == 5);
}
