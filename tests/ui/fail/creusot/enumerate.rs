//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/15_enumerate.rs` (3620de437): `Enumerate`, its `Iterator` impl,
// its `Invariant` and the constructor `enumerate`, with Creusot's code and Thrust's annotations.
// Creusot's `Invariant` impl is the `invariant` predicate of the `Iterator` impl, with the inner
// iterator's invariant added (Creusot's type invariant of the field); `resolve(&mut self.count)` in
// `completed` is `(*self).count == (!self).count`; `x@` of a `usize` is the integer itself.
// The struct has no `I: Iterator` bound: its model `Enumerate<I::Ty>` would need `I::Ty: Iterator`.
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Enumerate<I> {
    pub iter: I,
    pub count: usize,
}

impl<I: Model> Model for Enumerate<I> {
    type Ty = Enumerate<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
    I::Item: Model,
{
    type Item = (usize, I::Item);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
            && forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| forall(|i: <I as Model>::Ty|
                !I::produces(self.iter, s, i) || self.count + s.len() < usize::MAX))
            && forall(|i: Mut<<I as Model>::Ty>|
                !I::completed(i) || I::produces(*i, Seq::empty(), !i))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).count == (!self).count
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        visited.len() == o.count - self.count
            && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| {
                I::produces(self.iter, s, o.iter)
                    && visited.len() == s.len()
                    && forall(|i: Int| {
                        !(0 <= i && i < s.len())
                            || (visited[i].0 == self.count + i && visited[i].1 == s[i])
                    })
            })
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(x) => {
                let n = self.count;
                self.count += 1;
                // Unsat: the index is off by one, so `visited[i].0 == self.count + i` fails.
                Some((n + 1, x))
            }
        }
    }
}

// These two requirements are here only to prove the absence of overflow.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|i: Mut<<I as Model>::Ty>| !I::completed(i) || I::produces(*i, Seq::empty(), !i)))]
#[thrust_macros::requires(forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| forall(|i: <I as Model>::Ty|
    !I::produces(iter, s, i) || s.len() < usize::MAX)))]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::ensures(result.iter == iter && result.count == 0)]
#[thrust_macros::ensures(<Enumerate<I> as Iterator>::invariant(result))]
pub fn enumerate<I: Iterator>(iter: I) -> Enumerate<I>
where
    I::Item: Model,
{
    Enumerate { iter, count: 0 }
}
