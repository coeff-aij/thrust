//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens -A unused_imports
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

use std::marker::PhantomData;
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost};

pub struct DenseBitSet {
    words: Vec<u64>,
}

impl thrust_models::Model for DenseBitSet {
    type Ty = Int;
}

pub struct BitIter {
    word: u64,
}

impl thrust_models::Model for BitIter {
    type Ty = Int;
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result == *self && 0 <= *self)]
    fn iter(&self) -> BitIter {
        BitIter { word: 0 }
    }
}

impl Iterator for BitIter {
    type Item = usize;
    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<usize> {
        None
    }
}

#[thrust_macros::context]
impl IteratorSpec for BitIter {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        0 <= o && o + visited.len() == self
            && forall(|i: Int| !(0 <= i && i < visited.len()) || 0 <= visited[i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == 0 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}
// Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`, with a verified body. Like `all`
// it stops at the first item the closure rejects. `F: Fn` as in `Filter`, the closure's
// precondition must hold on every item the iterator can yield, and the items are `Copy` (the
// site iterates references), so the loop can record what it passed to the closure.
struct IterAllSpec<I, F>(PhantomData<(I, F)>);

#[thrust_macros::context]
impl<I, F> IterAllSpec<I, F>
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(e)))))
    }

    // `b` follows `a` by yielding `x`.
    #[thrust_macros::predicate]
    fn stepped(a: I, x: I::Item, b: I, func: F) -> bool {
        Self::pre_all(a, func) && I::produces(a, Seq::singleton(x), b)
    }

    // `pre_all` moves along one yielded item; the lemma is proved apart from the loop.
    #[thrust_macros::requires(Self::stepped(a, x, b, func))]
    #[thrust_macros::ensures(Self::pre_all(b, func))]
    fn pre_all_step(a: Ghost<I>, x: Ghost<I::Item>, b: Ghost<I>, func: Ghost<F>) {}

    #[thrust_macros::predicate]
    fn accepted(func: F, seen: Vec<I::Item>) -> bool {
        forall(|k: Int| !(0 <= k && k < seen.len()) || thrust_macros::post!(func(seen[k]), true))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter) && IterAllSpec::<I, F>::pre_all(iter, f))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>,
           mid: <I as thrust_models::Model>::Ty|
        I::produces(iter, visited, mid)
            && (result == true ==>
                exists(|fin: <I as thrust_models::Model>::Ty| I::completed(Mut::new(mid, fin)))
                    && forall(|k: Int| !(0 <= k && k < visited.len()) || thrust_macros::post!(f(visited[k]), true)))
            && (result == false ==>
                0 < visited.len()
                    && thrust_macros::post!(f(visited[visited.len() - 1]), false)
                    && forall(|k: Int| !(0 <= k && k < visited.len() - 1) || thrust_macros::post!(f(visited[k]), true))))
)]
fn iter_all<I, F>(iter: I, f: F) -> bool
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    I::produces_refl(&it);
    // `seen` records the items passed to the closure, for the loop invariant.
    let mut seen: Vec<I::Item> = Vec::new();
    loop {
        thrust_macros::invariant!(
            |it: I, seen: Vec<I::Item>, iter: thrust_models::FnParam<I>, f: F|
                I::inv(it)
                    && I::produces(iter.at_entry(), seen, it)
                    && IterAllSpec::<I, F>::accepted(f, seen)
                    && IterAllSpec::<I, F>::pre_all(it, f)
        );
        let before = thrust_macros::ghost!(|it: I| -> I { it });
        let Some(x) = it.next() else {
            return true;
        };
        let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
        let after = thrust_macros::ghost!(|it: I| -> I { it });
        let fs = thrust_macros::ghost!(|f: F| -> F { f });
        IterAllSpec::<I, F>::pre_all_step(before, yielded, after, fs);
        if !f(x) {
            return false;
        }
        seen.push(x);
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn small(set: &DenseBitSet) -> bool {
    iter_all(set.iter(), thrust_macros::closure!(requires(i < 100), ensures(true), |i: usize| -> bool { i < 100 }))
}

fn main() {}
