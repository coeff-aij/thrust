//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/02_iter_mut.rs` (3620de437): `IterMut`, its `Iterator` impl and the
// constructor `iter_mut`, with Creusot's code and Thrust's annotations. `invariant` is Creusot's
// `Invariant` impl; `iter_mut` states it of its result, which Creusot checks as the result's type
// invariant. `produces` states Creusot's `to_mut_seq` equation entry by entry.
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

#[path = "auxiliary/common.rs"]
mod common;
use common::Iterator;

struct IterMut<'a, T> {
    pub inner: &'a mut [T],
}

impl<'a, T: Model> Model for IterMut<'a, T> {
    type Ty = (Mut<Seq<<T as Model>::Ty>>,);
}

#[thrust_macros::context]
impl<'a, T> Iterator for IterMut<'a, T>
where
    T: Model + 'a,
{
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.split_off_first_mut()
    }

    // Creusot's type invariant of `IterMut`: the borrowed slice keeps its length.
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        (!self.0).len() == (*self.0).len()
    }

    // Creusot's `resolve(self.inner) && self.inner@.ext_eq(Seq::empty())` (creusot-rs/creusot
    // 3620de437, `examples/iterators/02_iter_mut.rs` line 24): the borrowed slice is resolved and
    // empty.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        !((*self).0) == *((*self).0) && *((*self).0) == Seq::empty()
    }

    // Creusot's `self.inner.to_mut_seq() == visited.concat(o.inner.to_mut_seq())`, index by index:
    // the visited pairs, then the rest of the slice.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (*self.0).len() == visited.len() + (*o.0).len()
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || visited[k] == Mut::new((*self.0)[k], (!self.0)[k]))
            && forall(|k: Int|
                !(0 <= k && k < (*o.0).len())
                    || ((*o.0)[k] == (*self.0)[visited.len() + k]
                        && (!o.0)[k] == (!self.0)[visited.len() + k]))
    }
}

// Creusot's constructor: the iterator's entry and final sequences are the vector's, and its type
// invariant holds.
#[thrust_macros::ensures(
    <IterMut<'a, T> as Iterator>::invariant(result)
        && *result.0 == *v
        && !result.0 == !v
)]
fn iter_mut<'a, T: Model>(v: &'a mut Vec<T>) -> IterMut<'a, T> {
    IterMut { inner: &mut v[..] }
}
