//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/06_map_precond.rs` (3620de437): `Map` with the history of the
// items it has taken, its `Iterator` impl, the predicates `next_precondition`, `preservation_inv`,
// `preservation` and `reinitialize`, and the constructor `map`, with Creusot's code and Thrust's
// annotations. Creusot's proof aids (`produces_one`, `produces_one_invariant` and the
// `proof_assert!` in `next`) have no counterpart: Thrust needs none. The model is the tuple
// (`iter`, `func`, `produced`): a struct model would need `I::Ty: Iterator` for `Map<I::Ty, _>`.
// `produces` relates the closure states as a sequence `fs` of `visited.len() + 1` states,
// equivalent to Creusot's `fs: Seq<&mut F>`, which gives no answer within 300 s here (fork issue
// #156). Creusot's clients `identity`, `increment` and `counter` are not ported (`counter` is
// `counter_creusot.rs`).
// Creusot's `inv(..)` premises of `next_precondition` (`inv(e)`), `preservation_inv`
// (`inv(s) && inv(e1) && inv(e2) && inv(f)`) and `map`'s `requires` are left out: Thrust has no invariant of a
// type parameter (the README's Type invariants), so they are vacuous at item types without an
// invariant, and these predicates are stronger than Creusot's where the item type has one.
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

#[path = "auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Map<I: Iterator, F> {
    pub iter: I,
    pub func: F,
    pub produced: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
}

impl<I: Iterator, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<<<I as Iterator>::Item as Model>::Ty>);
}

#[thrust_macros::context]
impl<I: Iterator, B: Model, F: FnMut(I::Item, Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>) -> B>
    Iterator for Map<I, F>
{
    type Item = B;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1, self.2)
            && Self::next_precondition(self.0, self.1, self.2)
            && I::invariant(self.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).2 == Seq::empty()
            && I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, succ: Self) -> bool {
        thrust_macros::hist_inv!(self.1, succ.1)
            && exists(|fs: Seq<Closure<F>>| exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
            fs.len() == visited.len() + 1
                && s.len() == visited.len()
                && I::produces(self.0, s, succ.0)
                && succ.2 == self.2.concat(s)
                && fs[0] == self.1
                && fs[visited.len()] == succ.1
                && forall(|i: Int|
                    !(0 <= i && i < visited.len())
                        || (thrust_macros::hist_inv!(self.1, fs[i])
                            && thrust_macros::post!(Mut::new(fs[i], fs[i + 1])(s[i], self.2.concat(s.subsequence(0, i))), visited[i])))))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                let produced = thrust_macros::ghost!(
                    |self: &mut Self, v: <I as Iterator>::Item|
                        -> Seq<<<I as Iterator>::Item as Model>::Ty> { (*self).2.push(v) });
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                Some(r)
            }
            None => {
                self.produced = thrust_macros::ghost!(|| -> Seq<<<I as Iterator>::Item as Model>::Ty> { Seq::empty() });
                None
            }
        }
    }
}

#[thrust_macros::context]
impl<I: Iterator, B: Model, F: FnMut(I::Item, Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>) -> B>
    Map<I, F>
{
    #[thrust_macros::predicate]
    pub fn next_precondition(iter: I, func: F, produced: Seq<<<I as Iterator>::Item as Model>::Ty>) -> bool {
        forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e, produced))))
    }

    // Creusot's `f: &mut F` is the pair of closure states `f1` (`*f`) and `f2` (`^f`).
    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F, produced: Seq<<<I as Iterator>::Item as Model>::Ty>) -> bool {
        forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as Model>::Ty|
        forall(|i: <I as Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::post!(Mut::new(f1, f2)(e1, produced.concat(s)), b))
                || thrust_macros::pre!(f2(e2, produced.concat(s).push(e1))))))))))
    }

    // Creusot's `preservation` is `preservation_inv` at the empty history, which Creusot's
    // `preservation_inv` ensures; it is defined so here.
    #[thrust_macros::predicate]
    pub fn preservation(iter: I, func: F) -> bool {
        Self::preservation_inv(iter, func, Seq::empty())
    }

    #[thrust_macros::predicate]
    pub fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|func: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, func, Seq::empty())
                    && Self::preservation(fin, func)))))
    }
}

// The type invariant Creusot checks of the result is stated as `ensures`, with the inner
// iterator's, which Creusot assumes of `iter`, as `requires`.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::requires(forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i2: <I as Model>::Ty|
    !I::produces(iter, Seq::singleton(e), i2) || thrust_macros::pre!(func(e, Seq::<<<I as Iterator>::Item as Model>::Ty>::empty())))))]
#[thrust_macros::requires(Map::<I, F>::reinitialize())]
#[thrust_macros::requires(Map::<I, F>::preservation(iter, func))]
#[thrust_macros::ensures(result.0 == iter && result.1 == func && result.2 == Seq::empty())]
#[thrust_macros::ensures(<Map<I, F> as Iterator>::invariant(result))]
pub fn map<I: Iterator, B: Model, F: FnMut(I::Item, Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, F> {
    Map { iter, func, produced: thrust_macros::ghost!(|| -> Seq<<<I as Iterator>::Item as Model>::Ty> { Seq::empty() }) }
}
