//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

// Creusot's `examples/iterators/02_iter_mut.rs` (creusot-rs/creusot 3620de437): an iterator over a
// mutable slice, `IterMut { inner: &mut [T] }` (lines 7-9), whose `next` hands out the first element
// by `split_off_first_mut` and keeps the rest (lines 48-54). Its model is the model of `inner`, the
// slice's current and final sequences. The associated `Item` is `&'a mut T`, so `visited` is a
// sequence of `Mut` pairs.

// Creusot's constructor `iter_mut(v)`, `IterMut { inner: &mut v[..] }` (lines 64-69), and its
// `all_zero` client (lines 71-88) follow the impl. The constructor's `invariant` needs that
// `&mut v[..]` keeps the length, which std.rs states for `IndexMut`.

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

    fn next(&mut self) -> Option<Self::Item> {
        (self.inner).split_off_first_mut()
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

#[thrust_macros::context]
impl<'a, T> IterMut<'a, T>
where
    T: Model,
{
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
fn iter_mut<'a, T>(v: &'a mut Vec<T>) -> IterMut<'a, T>
where
    T: Model,
{
    IterMut { inner: &mut v[..] }
}

// Creusot's `all_zero` over that iterator: `iter_mut(v).into_iter()`, then `next` until `None`. The positions
// passed, the vector's length minus what the iterator has left, are zero in the final sequence.
#[thrust_macros::context]
#[thrust_macros::ensures(
    (!v).len() == (*v).len()
        && forall(|i: Int| (0 <= i && i < (!v).len()) ==> ((!v)[i] == 0))
)]
fn all_zero(v: &mut Vec<usize>) {
    let mut it = iter_mut(v).into_iter();
    loop {
        thrust_macros::invariant!(
            |it: IterMut<'_, usize>, v: thrust_models::FnParam<&mut Vec<usize>>|
                (!v.at_entry()).len() == (*v.at_entry()).len()
                    && (*it.0).len() <= (*v.at_entry()).len()
                    && (!it.0).len() == (*it.0).len()
                    && forall(|j: Int| !(0 <= j && j < (*it.0).len())
                        || ((*it.0)[j] == (*v.at_entry())[(*v.at_entry()).len() - (*it.0).len() + j]
                            && (!it.0)[j] == (!v.at_entry())[(*v.at_entry()).len() - (*it.0).len() + j]))
                    && forall(|j: Int| (0 <= j && j < (*v.at_entry()).len() - (*it.0).len())
                        ==> ((!v.at_entry())[j] == 0))
        );
        match it.next() {
            Some(x) => {
                *x = 0;
            }
            None => break,
        }
    }
}

fn main() {}
