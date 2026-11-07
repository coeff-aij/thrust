//@error-in-other-file: Unsat
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `MapInv` (3620de437, `examples/iterators/06_map_precond.rs`): the closure receives the
// ghost history `produced` of the inner items consumed so far, so its precondition may depend on
// it. `produces` extends `produced` by the existential input sequence `s` and calls the closure at
// the history `produced ++ s[..k]` for the `k`-th item; the invariant is Creusot's `reinitialize`,
// `preservation_inv`, the inner invariant and `next_precondition`, which Creusot states as `Map`'s
// type invariant and `map` here ensures of its result. The closure is `FnMut`: `produces` carries
// the chain `fs` of closure states related by `hist_inv!` (Creusot's `hist_inv`), and
// `preservation_inv` and `reinitialize` quantify over every closure state. Both laws are inherited
// and checked at the impl with no lemma.
//
// Fail twin: `next` does not extend `produced` by the consumed item.

#[path = "../../pass/creusot/common.rs"]
mod common;
use common::Iterator;

pub struct Map<I: Iterator, F>
where
    <I as Iterator>::Item: Model,
{
    pub iter: I,
    pub func: F,
    pub produced: Ghost<Seq<<I::Item as Model>::Ty>>,
}

// The model is the tuple (iter, func, produced), read as `.0`, `.1`, `.2` in the specifications;
// a struct model `Map<I::Ty, ..>` would need `I::Ty: Iterator`.
impl<I: Iterator, F> Model for Map<I, F>
where
    <I as Iterator>::Item: Model,
{
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<<I::Item as Model>::Ty>);
}

#[thrust_macros::context]
impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<<I::Item as Model>::Ty>>) -> B> Iterator for Map<I, F>
where
    B: Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    type Item = B;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).2 == Seq::empty()
            && I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    // Creusot's `produces`: the inner items `s`, the closure states `fs` with `fs[k]` before and
    // `fs[k + 1]` after the `k`-th call, and the history `produced ++ s[..k]` at the `k`-th call.
    // Creusot's `fs: Seq<&mut F>` (read as `*fs[k]` and `^fs[k]`) can be written, but gives no
    // answer within 300 s once `preservation_inv` has no `pre!` premise; the sequence of states
    // answers.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| exists(|fs: Seq<Closure<F>>|
            s.len() == visited.len()
                && I::produces(self.0, s, o.0)
                && o.2 == self.2.concat(s)
                && fs.len() == visited.len() + 1
                && fs[0] == self.1
                && fs[visited.len()] == o.1
                && forall(|k: Int|
                    !(0 <= k && k < visited.len())
                        || (thrust_macros::hist_inv!(self.1, fs[k])
                            && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k], self.2.concat(s.subsequence(0, k))), visited[k])))))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                let produced = thrust_macros::ghost!(|self: &mut Self, v: I::Item| -> Seq<<I::Item as Model>::Ty> { (*self).2 });
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                Some(r)
            }
            None => {
                self.produced = thrust_macros::ghost!(|| -> Seq<<I::Item as Model>::Ty> { Seq::empty() });
                None
            }
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1, self.2)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1, self.2)
    }
}

#[thrust_macros::context]
impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<<I::Item as Model>::Ty>>) -> B> Map<I, F>
where
    B: Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    #[thrust_macros::predicate]
    pub fn next_precondition(iter: I, func: F, produced: Seq<<I::Item as Model>::Ty>) -> bool {
        forall(|e: <I::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e, produced))))
    }

    // Creusot's `preservation_inv` (and, at `produced == []`, `preservation`), over every closure
    // state `f1` that `func` reaches (`func.hist_inv(*f)`) and its successor `f2` (Creusot's
    // `f: &mut F`).
    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F, produced: Seq<<I::Item as Model>::Ty>) -> bool {
        forall(|s: Seq<<I::Item as Model>::Ty>|
        forall(|e1: <I::Item as Model>::Ty|
        forall(|e2: <I::Item as Model>::Ty|
        forall(|i: <I as Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::post!(Mut::new(f1, f2)(e1, produced.concat(s)), b))
                || thrust_macros::pre!(f2(e2, produced.concat(s).push(e1))))))))))
    }

    // Creusot's `reinitialize`: after completion (`produced` reset to []), the next item's
    // precondition and preservation hold again, for every closure state.
    #[thrust_macros::predicate]
    pub fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f, Seq::empty())
                    && Self::preservation_inv(fin, f, Seq::empty())))))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(forall(|e: <I::Item as Model>::Ty| forall(|i2: <I as Model>::Ty|
    I::produces(iter, Seq::singleton(e), i2) ==> thrust_macros::pre!(func(e, Seq::<<I::Item as Model>::Ty>::empty())))))]
#[thrust_macros::requires(Map::<I, F>::reinitialize())]
#[thrust_macros::requires(Map::<I, F>::preservation_inv(iter, func, Seq::empty()))]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::ensures(result.0 == iter && result.1 == func && result.2 == Seq::empty())]
#[thrust_macros::ensures(<Map<I, F> as Iterator>::invariant(result))]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<<I::Item as Model>::Ty>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, F>
where
    B: Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    Map { iter, func, produced: thrust_macros::ghost!(|| -> Seq<<I::Item as Model>::Ty> { Seq::empty() }) }
}
