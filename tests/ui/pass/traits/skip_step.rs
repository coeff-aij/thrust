//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::{Int, Seq};
use thrust_models::{exists, forall, Model};

// The step form of the iterator spec (`skip.rs` is the Creusot form) on the same `Skip` adapter.
// `next` follows std's implementation: it stops as soon as the inner iterator is exhausted while
// draining, and `completed`/`step` describe the drained states as a chain of inner steps.
#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

pub struct Skip<I> {
    iter: I,
    n: usize,
}

impl<I: Model> Model for Skip<I> {
    type Ty = (<I as Model>::Ty, Int);
}

#[thrust_macros::context]
impl<I> Iterator for Skip<I>
where
    I: Iterator + Model,
    <I as Model>::Ty: PartialEq,
    <I as Iterator>::Item: Model,
    <<I as Iterator>::Item as Model>::Ty: PartialEq,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        let s = self;
        let mut n = s.n;
        s.n = 0;
        loop {
            // The inner states reached so far form a chain of `step`s from the entry state to the
            // current one; `n` counts the items still to drain.
            thrust_macros::invariant!(
                |s: &mut Skip<I>, n: usize, self: thrust_models::FnParam<&mut Skip<I>>|
                    !s == !self.at_entry()
                        && (*s).1 == 0
                        && I::invariant((*s).0)
                        && 0 <= n
                        && n <= (*self.at_entry()).1
                        && exists(|t: Seq<<I as Model>::Ty>|
                            t.len() == (*self.at_entry()).1 - n + 1
                                && t[0] == (*self.at_entry()).0
                                && t[t.len() - 1] == (*s).0
                                && forall(|k: Int| (0 <= k && k < t.len() - 1) ==>
                                    exists(|i: <<I as Iterator>::Item as Model>::Ty| I::step(t[k], i, t[k + 1]))))
            );
            let r = s.iter.next();
            if n == 0 {
                return r;
            }
            match r {
                None => return None,
                Some(_) => {}
            }
            n -= 1;
        }
    }

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
            (q_invariant_d03ea8f3740b0e7ef4cf484267be8763<a0> (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0))";
        true
    }

    // (!self).n == 0
    // && exists iters m. 0 <= m <= (*self).n && iters[0] == (*self).iter
    //    && (forall k. 0 <= k < m ==> exists i. iters[k].step(i, iters[k + 1]))
    //    && I::completed(Mut::new(iters[m], (!self).iter))
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (= (tuple_proj<a0-Int>.1 (mut_final<Tuple<a0-Int>> self_)) 0)
            (exists ((iters (Array Int a0)) (m Int))
                (and
                    (<= 0 m)
                    (<= m (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)))
                    (= (select iters 0) (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_)))
                    (forall ((k Int))
                        (=> (and (<= 0 k) (< k m))
                            (exists ((i a1))
                                (q_step_d03ea8f3740b0e7ed05d2c0199833fd7<a0> (select iters k) i (select iters (+ k 1))))))
                    (q_completed_d03ea8f3740b0e7eea0667c762a7cc04<a0>
                        (mut<a0> (select iters m) (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_)))))))";
        true
    }

    // dist.n == 0
    // && exists iters. iters[0] == self.iter
    //    && (forall k. 0 <= k < self.n ==> exists i. iters[k].step(i, iters[k + 1]))
    //    && iters[self.n].step(item, dist.iter)
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(and
            (= (tuple_proj<a0-Int>.1 dist) 0)
            (exists ((iters (Array Int a0)))
                (and
                    (= (select iters 0) (tuple_proj<a0-Int>.0 self_))
                    (forall ((k Int))
                        (=> (and (<= 0 k) (< k (tuple_proj<a0-Int>.1 self_)))
                            (exists ((i a1))
                                (q_step_d03ea8f3740b0e7ed05d2c0199833fd7<a0> (select iters k) i (select iters (+ k 1))))))
                    (q_step_d03ea8f3740b0e7ed05d2c0199833fd7<a0> (select iters (tuple_proj<a0-Int>.1 self_)) item (tuple_proj<a0-Int>.0 dist)))))";
        true
    }
}

fn main() {}
