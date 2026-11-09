//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/05_map.rs` (3620de437): `Map`, its `Iterator` impl, the
// predicates `next_precondition`, `preservation` and `reinitialize`, and the constructor `map`,
// with Creusot's code and Thrust's annotations. Creusot's proof aids (`produces_one`,
// `produces_one_invariant` and the `proof_assert!` in `next`) have no counterpart: Thrust needs
// none. `produces` relates the closure states as a sequence `fs` of `visited.len() + 1` states,
// equivalent to Creusot's `fs: Seq<&mut F>`; Creusot's form gives no answer within 300 s here
// (fork issue #156).
// Creusot's `inv(..)` premises of `next_precondition` (`inv(e)`), `preservation`
// (`inv(s) && inv(e1) && inv(e2) && inv(f)`) and `map`'s `requires` are left out: Thrust has no invariant of a
// type parameter (the README's Type invariants), so they are vacuous at item types without an
// invariant, and these predicates are stronger than Creusot's where the item type has one.
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

#[path = "auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Map<I, F> {
    pub iter: I,
    pub func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = Map<<I as Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I: Iterator, B: Model, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    type Item = B;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation(self.iter, self.func)
            && Self::next_precondition(self.iter, self.func)
            && I::invariant(self.iter)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, succ: Self) -> bool {
        thrust_macros::hist_inv!(self.func, succ.func)
            && exists(|fs: Seq<Closure<F>>| exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
            fs.len() == visited.len() + 1
                && s.len() == visited.len()
                && I::produces(self.iter, s, succ.iter)
                && fs[0] == self.func
                && fs[visited.len()] == succ.func
                && forall(|i: Int|
                    !(0 <= i && i < visited.len())
                        || (thrust_macros::hist_inv!(self.func, fs[i])
                            && thrust_macros::post!(Mut::new(fs[i], fs[i + 1])(s[i]), visited[i])))))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }
}

#[thrust_macros::context]
impl<I: Iterator, B: Model, F: FnMut(I::Item) -> B> Map<I, F> {
    #[thrust_macros::predicate]
    pub fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    // Creusot's `f: &mut F` is the pair of closure states `f1` (`*f`) and `f2` (`^f`).
    #[thrust_macros::predicate]
    pub fn preservation(iter: I, func: F) -> bool {
        forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as Model>::Ty|
        forall(|i: <I as Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    #[thrust_macros::predicate]
    pub fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|func: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, func) && Self::preservation(fin, func)))))
    }
}

// The type invariant Creusot checks of the result is stated as `ensures`, with the inner
// iterator's, which Creusot assumes of `iter`, as `requires`.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::requires(forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i2: <I as Model>::Ty|
    !I::produces(iter, Seq::singleton(e), i2) || thrust_macros::pre!(func(e)))))]
#[thrust_macros::requires(Map::<I, F>::reinitialize())]
#[thrust_macros::requires(Map::<I, F>::preservation(iter, func))]
#[thrust_macros::ensures(result.iter == iter && result.func == func)]
#[thrust_macros::ensures(<Map<I, F> as Iterator>::invariant(result))]
pub fn map<I: Iterator, B: Model, F: FnMut(I::Item) -> B>(iter: I, func: F) -> Map<I, F> {
    Map { iter, func }
}
