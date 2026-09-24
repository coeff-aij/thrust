//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::forall;
use thrust_models::model::Seq;
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

// Sorts in the bodies: a0 = T. The model is (Seq<a0>, Seq<a0>, Int): the entry and final
// sequences of the slice, and the cursor.
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
        "(and
            (<= 0 (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 self_))
            (<= (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 self_)
                (seq.len
                    (tuple_proj<Seq<a0>-Seq<a0>-Int>.0 self_))))";
        true
    }

    // (*self).2 >= (*self).0.len() && *self == !self
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (>= (tuple_proj<Seq<a0>-Seq<a0>-Int>.2
                    (mut_current<Tuple<Seq<a0>-Seq<a0>-Int>> self_))
                (seq.len
                    (tuple_proj<Seq<a0>-Seq<a0>-Int>.0
                        (mut_current<Tuple<Seq<a0>-Seq<a0>-Int>> self_))))
            (= (mut_current<Tuple<Seq<a0>-Seq<a0>-Int>> self_)
               (mut_final<Tuple<Seq<a0>-Seq<a0>-Int>> self_)))";
        true
    }

    // o.0 == self.0 && o.1 == self.1 && o.2 == self.2 + visited.len()
    // && forall k. 0 <= k < visited.len() ==>
    //        visited[k] == Mut(self.0[self.2 + k], self.1[self.2 + k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
            (= (tuple_proj<Seq<a0>-Seq<a0>-Int>.0 o)
               (tuple_proj<Seq<a0>-Seq<a0>-Int>.0 self_))
            (= (tuple_proj<Seq<a0>-Seq<a0>-Int>.1 o)
               (tuple_proj<Seq<a0>-Seq<a0>-Int>.1 self_))
            (= (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 o)
               (+ (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 self_)
                  (seq.len visited)))
            (forall ((k Int))
                (=> (and (<= 0 k) (< k (seq.len visited)))
                    (= (seq.nth visited k)
                       (mut<a0>
                           (seq.nth (tuple_proj<Seq<a0>-Seq<a0>-Int>.0 self_)
                                   (+ (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 self_) k))
                           (seq.nth (tuple_proj<Seq<a0>-Seq<a0>-Int>.1 self_)
                                   (+ (tuple_proj<Seq<a0>-Seq<a0>-Int>.2 self_) k)))))))";
        true
    }
}

fn main() {}
