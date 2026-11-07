//@check-pass
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `Map` (3620de437, `examples/iterators/05_map.rs`) over an `FnMut` closure, fully
// checked: `produces` carries the chain `fs` of closure states and relates them by `hist_inv!`
// (Creusot's `hist_inv`), and `preservation` and `reinitialize` quantify over every closure state.
// Both laws are inherited and checked at the impl with no lemma. Creusot's type invariant of `Map`
// is the `invariant` predicate, which `map` ensures of its result.

mod common;
use common::Iterator;

pub struct Map<I, F> {
    // The inner iterator
    pub iter: I,
    // The mapper
    pub func: F,
}

// The model is the tuple (iter, func), read as `.0`, `.1` in the specifications.
impl<I: Model, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I: Iterator, B, F: FnMut(I::Item) -> B> Iterator for Map<I, F>
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
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    // Creusot's `produces`: the inner items `s`, the closure states `fs` with `fs[k]` before and
    // `fs[k + 1]` after the `k`-th call. Creusot's `fs: Seq<&mut F>` (read as `*fs[k]` and
    // `^fs[k]`) can be written, but gives no answer within 300 s once `preservation` has no
    // `pre!(f1(e1))` premise; the sequence of states answers.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| exists(|fs: Seq<Closure<F>>|
            s.len() == visited.len()
                && I::produces(self.0, s, o.0)
                && fs.len() == visited.len() + 1
                && fs[0] == self.1
                && fs[visited.len()] == o.1
                && forall(|k: Int|
                    !(0 <= k && k < visited.len())
                        || (thrust_macros::hist_inv!(self.1, fs[k])
                            && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some((self.func)(v))
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation(self.0, self.1)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1)
    }
}

#[thrust_macros::context]
impl<I: Iterator, B, F: FnMut(I::Item) -> B> Map<I, F>
where
    B: Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    #[thrust_macros::predicate]
    pub fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    // Creusot's `preservation`, over every closure state `f1` that `func` reaches
    // (`func.hist_inv(*f)`) and its successor `f2` (Creusot's `f: &mut F`).
    #[thrust_macros::predicate]
    pub fn preservation(iter: I, func: F) -> bool {
        forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|i: <I as Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    // Creusot's `reinitialize`: after completion, the next item's precondition and preservation
    // hold again, for every closure state.
    #[thrust_macros::predicate]
    pub fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f)
                    && Self::preservation(fin, f)))))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i2: <I as Model>::Ty|
    I::produces(iter, Seq::singleton(e), i2) ==> thrust_macros::pre!(func(e)))))]
#[thrust_macros::requires(Map::<I, F>::reinitialize())]
#[thrust_macros::requires(Map::<I, F>::preservation(iter, func))]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::ensures(result.0 == iter && result.1 == func)]
#[thrust_macros::ensures(<Map<I, F> as Iterator>::invariant(result))]
pub fn map<I: Iterator, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> Map<I, F>
where
    B: Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    Map { iter, func }
}
