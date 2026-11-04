//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// One extern spec covers the target `<Seq<i64> as Index<R>>::index` at every key type, with the
// contract each key type gives through the spec trait `KeyValue`. Two specs of one target that
// could cover one instance are rejected (`fail/extern_spec_overlap_*.rs`).

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

impl<T> Key<T> for u8 {
    type Output = usize;

    fn key(self) -> usize {
        self as usize
    }
}

#[thrust_macros::context]
trait KeyValue: thrust_models::Model {
    #[thrust_macros::predicate]
    fn has_value(self, out: i64) -> bool;
}

#[thrust_macros::context]
impl KeyValue for usize {
    #[thrust_macros::predicate]
    fn has_value(self, out: i64) -> bool {
        out == 5
    }
}

#[thrust_macros::context]
impl KeyValue for u8 {
    #[thrust_macros::predicate]
    fn has_value(self, out: i64) -> bool {
        out == 7
    }
}

struct Seq<T> {
    raw: Vec<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for Seq<T> {
    type Ty = <Vec<T> as thrust_models::Model>::Ty;
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
#[thrust_macros::ensures(R::has_value(index, *result))]
fn _extern_spec_seq_index<R: Key<i64, Output = usize> + KeyValue>(
    s: &Seq<i64>,
    index: R,
) -> &i64 {
    <Seq<i64> as Index<R>>::index(s, index)
}

fn main() {
    let s: Seq<i64> = Seq { raw: Vec::new() };
    assert!(s[0_usize] == 5);
    assert!(s[0_u8] == 5);
}
