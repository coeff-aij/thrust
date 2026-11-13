//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// The fail twin of `pass/all_zero_loop.rs`: the postcondition claims every element ends up 1.
// Creusot's `examples/iterators/02_iter_mut.rs` (3620de437) with its client `all_zero`, with
// Creusot's code and Thrust's annotations: the hand-written `loop` over Creusot's own `IterMut`,
// concrete. `IterMut`'s impl and `iter_mut` are those of `tests/ui/pass/creusot/iter_mut.rs`.
// `snapshot!` is `ghost!`. The invariant also states what Creusot keeps from the snapshot and
// carries as type invariants: `iter_old` is the vector's borrow, and `IterMut`'s `invariant` holds
// of `iter_old` and `it`.
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq, UInt};
use thrust_models::{FnParam, Ghost, Model};

#[path = "../../../../tests/ui/pass/creusot/auxiliary/common.rs"]
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

    // Creusot's `resolve(self.inner) && self.inner@.ext_eq(Seq::empty())`: the borrowed slice is
    // resolved and empty.
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

#[thrust_macros::context]
impl<'a, T: Model> IterMut<'a, T> {
    #[thrust_macros::ensures(result == self)]
    fn into_iter(self) -> Self {
        self
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

#[thrust_macros::context]
#[thrust_macros::ensures((!v).len() == (*v).len())]
#[thrust_macros::ensures(forall(|i: Int| 0 <= i && i < (*v).len() ==> (!v)[i] == 1))]
pub fn all_zero(v: &mut Vec<usize>) {
    let mut it = iter_mut(v).into_iter();
    let iter_old = thrust_macros::ghost!(|it: IterMut<'_, usize>| -> IterMut<'_, usize> { it });
    let mut produced = thrust_macros::ghost!(|| -> Seq<Mut<UInt>> { Seq::empty() });
    loop {
        thrust_macros::invariant!(|it: IterMut<'_, usize>, iter_old: Ghost<IterMut<'_, usize>>, produced: Ghost<Seq<Mut<UInt>>>, v: FnParam<&mut Vec<usize>>|
            *iter_old.0 == *v.at_entry() && !iter_old.0 == !v.at_entry()
                && <IterMut<'_, usize> as Iterator>::invariant(iter_old)
                && <IterMut<'_, usize> as Iterator>::invariant(it)
                && <IterMut<'_, usize> as Iterator>::produces(iter_old, produced, it)
                && forall(|i: Int| 0 <= i && i < produced.len() ==> !produced[i] == 0));
        match it.next() {
            Some(x) => {
                produced = thrust_macros::ghost!(|produced: Ghost<Seq<Mut<UInt>>>, x: &mut usize| -> Seq<Mut<UInt>> { produced.concat(Seq::singleton(x)) });
                *x = 0;
            }
            None => break,
        }
    }
}
