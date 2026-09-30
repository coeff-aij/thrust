//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:804d76744
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

// Creusot's `iter_mut.rs`: the iterator specification implemented for `core::slice::IterMut`,
// whose model is the slice's entry and final sequences and a cursor. `next` is std's; its
// contract is the extern spec. The associated `Item` is `&'a mut T`, so `visited` is a sequence
// of `Mut` pairs.

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

// The model is (Seq<T>, Seq<T>, Int): the entry and final sequences of the slice, and the cursor.
#[thrust_macros::context]
impl<'a, T> Iterator for core::slice::IterMut<'a, T>
where
    T: Model + 'a,
    <T as Model>::Ty: PartialEq,
{
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        <core::slice::IterMut<'a, T> as std::iter::Iterator>::next(self)
    }



    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.2 && self.2 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).2 >= (*self).0.len() && *self == !self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        o.0 == self.0
            && o.1 == self.1
            && o.2 == self.2 + visited.len()
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || visited[k] == Mut::new(self.0[self.2 + k], self.1[self.2 + k]))
    }
}

fn main() {}
