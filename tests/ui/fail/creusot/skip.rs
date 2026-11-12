//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/04_skip.rs` (3620de437): `Skip` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations, except that `next` has the control flow of the 2022
// artifact's `iterators/skip.rs` (`if n == 0 || r.is_none() { return r; } n -= 1`), and the ghost
// `skipped` updated after the check by a formula `match` on `r`, so that `next`'s executable code
// is the artifact's, apart from moving `self` into `s` first (below). `invariant` states the inner
// iterator's, which Creusot carries as the type invariant of the field. The loop's `invariant!`
// states Creusot's invariants over the ghost `skipped` and what Creusot keeps without writing it:
// `self.n` stays 0, the inner iterator's `invariant`, and `self`'s final value and `old_self` equal
// to those of the parameter at entry, which only a `FnParam` binder named `self` can name; the
// loop therefore uses `s`, the `&mut` moved out of `self`. Creusot's third invariant
// and the `resolve` of the skipped items in `completed` and `produces` have no counterpart: Thrust
// has no `resolve` predicate (fork issue #156).
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, Ghost, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Skip<I> {
    pub iter: I,
    pub n: usize,
}

impl<I: Model> Model for Skip<I> {
    type Ty = Skip<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Skip<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).n == 0
            && exists(|s: Seq<<Self::Item as Model>::Ty>| exists(|i: <I as Model>::Ty|
                s.len() <= (*self).n
                    && I::produces((*self).iter, s, i)
                    && I::completed(Mut::new(i, (!self).iter))))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (visited.len() == 0 && self == o)
            || (o.n == 0
                && visited.len() > 0
                && exists(|s: Seq<<Self::Item as Model>::Ty>|
                    s.len() == self.n
                        && I::produces(self.iter, s.concat(visited), o.iter)))
    }

    fn next(&mut self) -> Option<I::Item> {
        let s = self;
        let old_self = thrust_macros::ghost!(|s: &mut Self| -> Self { *s });
        let mut n = std::mem::take(&mut s.n);
        let mut skipped = thrust_macros::ghost!(|| -> Seq<<<I as Iterator>::Item as Model>::Ty> { Seq::empty() });
        loop {
            thrust_macros::invariant!(
                |s: &mut Self, n: usize, old_self: Ghost<Self>, skipped: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, self: thrust_models::FnParam<&mut Self>|
                    skipped.len() + n == old_self.n
                        && I::produces(old_self.iter, skipped, (*s).iter)
                        && (*s).n == 0
                        && I::invariant((*s).iter)
                        && !s == !self.at_entry()
                        && old_self == *self.at_entry()
            );
            let r = s.iter.next();
            // Unsat: one item fewer is skipped.
            if n <= 1 || r.is_none() {
                return r;
            }
            skipped = thrust_macros::ghost!(|skipped: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, r: Option<I::Item>| -> Seq<<<I as Iterator>::Item as Model>::Ty> { match r { Some(x) => skipped.push(x), None => skipped } });
            n -= 1
        }
    }
}
