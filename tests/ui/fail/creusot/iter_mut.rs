//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

// Creusot's `iter_mut.rs`: the iterator spec (`produces` / `completed` / `invariant`, laws as
// ensures on `next`) implemented for `core::slice::IterMut`, whose model is the slice's entry
// and final sequences and a cursor. `next` is std's; its contract is the extern spec. The
// associated `Item` is `&'a mut T`, so `visited` is a sequence of `Mut` pairs.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(Self::produces(*self, Seq::empty(), *self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        result == Some(i) && Self::produces(a, s, *self) ==> Self::produces(a, s.push(i), !self)))))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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

    fn produces_refl(a: &core::slice::IterMut<'a, T>) {}

    // 0 <= self.2 && self.2 <= self.0.len()
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.2 && self.2 <= self.0.len()
    }

    // (*self).2 >= (*self).0.len() && *self == !self
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).2 >= (*self).0.len() && *self == !self
    }

    // o.0 == self.0 && o.1 == self.1 && o.2 == self.2 + visited.len()
    // && forall k. 0 <= k < visited.len() ==>
    //        visited[k] == Mut(self.0[k], self.1[k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        o.0 == self.0
            && o.1 == self.1
            && o.2 == self.2 + visited.len()
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || visited[k] == Mut::new(self.0[k], self.1[k]))
    }
}

fn main() {}
