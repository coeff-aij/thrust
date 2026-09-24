//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// Iterating a transparently modelled newtype's sequence field mutably, and stating the result
// about the whole value rather than about the field: `v.raw` is the very sequence `v` is, so
// `it.0` and `it.1` -- the entry and final sequences `slice::IterMut` was made from -- are
// `v`'s own entry and final values, and what the loop writes through the iterator is what `!v`
// ends up holding.

use std::marker::PhantomData;

use thrust_models::forall;
use thrust_models::model::Int;

struct Idx;

struct IndexVec<I, T> {
    raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I, T> thrust_models::Model for IndexVec<I, T>
where
    T: thrust_models::Model,
{
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
#[thrust_macros::requires((*v).len() >= 0)]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|j: Int| (0 <= j && j < (!v).len()) ==> ((!v)[j] == 0))
)]
fn clear(v: &mut IndexVec<Idx, i64>) {
    let mut it = v.raw.iter_mut();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: core::slice::IterMut<'_, i64>, v: thrust_models::FnParam<&mut IndexVec<Idx, i64>>|
                it.0 == *v.at_entry()
                    && it.1 == !v.at_entry()
                    && it.1.len() == it.0.len()
                    && it.2 <= it.0.len()
                    && forall(|j: Int| (0 <= j && j < it.2) ==> (it.1[j] == 0))
        );
        *x = 0;
    }
}

fn main() {}
