//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

// Creusot's `iter_mut.rs`: an iterator over a mutable slice, `IterMut { inner: &mut [T] }`, whose
// `next` hands out the first element by `split_off_first_mut` and keeps the rest. Its model is the
// model of `inner`, the slice's current and final sequences. The associated `Item` is `&'a mut T`,
// so `visited` is a sequence of `Mut` pairs.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, which every impl
// inherits and Thrust checks at each impl (Creusot restates them per impl with empty bodies), and
// `next` with Creusot's contract.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;
}

struct IterMut<'a, T> {
    inner: &'a mut [T],
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

    // The 2022 artifact's `self.resolve()` and the current Creusot's `resolve(self.inner)`, and the
    // slice is empty.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && !((*self).0) == *((*self).0) && *((*self).0) == Seq::empty()
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

fn main() {}
