//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

/// The model of `u32`, which carries its width while `THRUST_INT_RANGE` is set.
#[cfg(not(thrust_int_range))]
type U32 = thrust_models::model::UInt;
#[cfg(thrust_int_range)]
type U32 = thrust_models::model::UIntN<32>;

// Fail twin: the client asserts `cnt == x.len() + 1`.
// Creusot's `counter` (`examples/iterators/03_std_iterators.rs`, 3620de437), with Creusot's
// client and its three assertions: `v.iter().map_inv(|x, _prod| { cnt += 1; *x }).collect()`, then
// `x == v` and `cnt == x.len()`. `Map` is creusot-std's `MapInv` (`std/iter/map_inv.rs`), built
// by `map_inv`, over an `FnMut` closure: `produces` relates the closure states as a sequence `fs`
// of `visited.len() + 1` states, equivalent to Creusot's `fs: Seq<&mut F>`, each related to the
// first by `hist_inv!` (Creusot's `hist_inv`). The source is std's `slice::Iter<u32>`, an iterator
// of the local spec through its std.rs model. `collect` is trusted, as creusot-std's is; it takes
// `&mut self` and ensures the final state completed, where Creusot's by-value `collect` ensures
// `resolve(^done)`: Thrust has no `resolve` (fork issue #156), and the final state carries the
// prophecy of the borrow of `cnt`.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, which every impl
// inherits and Thrust checks at each impl (Creusot restates them per impl with empty bodies), and
// `next` with Creusot's contract.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    // Creusot's `collect` (iter.rs), an extern spec and so trusted: `exists done prod.
    // resolve(^done) && done.completed() && self.produces(prod, *done) && B::from_iter_post(prod,
    // result)`, with `from_iter_post` for `Vec` (vec.rs) `prod == res@` folded in: `result` is the
    // produced sequence, a `Vec`, the one collection the cases build. `&mut self`: the caller keeps
    // the adapter. A loop that builds the `Vec` is checked in `collect_for.rs`, Creusot's `collect`.
    #[thrust::trusted]
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty|
        Self::produces(*self, result, pre) && Self::completed(Mut::new(pre, !self))))]
    fn collect(&mut self) -> Vec<Self::Item>
    where
        Self: Sized,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        let mut v = Vec::new();
        while let Some(x) = self.next() {
            v.push(x);
        }
        v
    }

    // creusot-std's `map_inv` (`std/iter.rs`): the adapter over `self` and `func` with an empty
    // history. Creusot requires the adapter's type invariant here; `collect` requires it.
    #[thrust_macros::ensures(result.0 == self && result.1 == func && result.2 == Seq::empty())]
    fn map_inv<B, F>(self, func: F) -> Map<Self, <Self::Item as Model>::Ty, F>
    where
        Self: Sized,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
        F: FnMut(Self::Item, Ghost<Seq<<Self::Item as Model>::Ty>>) -> B,
    {
        Map {
            iter: self,
            func,
            produced: thrust_macros::ghost!(|| -> Seq<<Self::Item as Model>::Ty> { Seq::empty() }),
        }
    }
}

struct Map<I, A, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<A>>,
}

// The model is the tuple (iter, func, produced), read as `.0`, `.1`, `.2` in the specifications.
impl<I: Model, A, F> Model for Map<I, A, F> {
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<A>);
}

#[thrust_macros::context]
impl<I, A, B, F> Map<I, A, F>
where
    I: Iterator + Model,
    A: Model<Ty = A>,
    B: Model,
    F: FnMut(I::Item, Ghost<Seq<A>>) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F, produced: Seq<A>) -> bool {
        forall(|e: A| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e, produced))))
    }

    // Creusot's `preservation_inv` (and, at `produced == []`, `preservation`), over every closure
    // state `f1` that `func` reaches (`func.hist_inv(*f)`) and its successor `f2` (Creusot's
    // `f: &mut F`).
    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F, produced: Seq<A>) -> bool {
        forall(|s: Seq<A>|
        forall(|e1: A|
        forall(|e2: A|
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
    fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f, Seq::empty())
                    && Self::preservation_inv(fin, f, Seq::empty())))))
    }

}

#[thrust_macros::context]
impl<I, A, B, F> Iterator for Map<I, A, F>
where
    I: Iterator + Model,
    A: Model<Ty = A>,
    B: Model,
    F: FnMut(I::Item, Ghost<Seq<A>>) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty>,
{
    type Item = B;

    // Creusot's `next`: the closure is called with the history before `v`, then `v` is pushed;
    // on `None` the history is reset.
    fn next(&mut self) -> Option<B> {
        match self.iter.next() {
            Some(v) => {
                let produced = thrust_macros::ghost!(
                    |self: &mut Self, v: <I as Iterator>::Item| -> Seq<A> { (*self).2.push(v) });
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                Some(r)
            }
            None => {
                self.produced = thrust_macros::ghost!(|| -> Seq<A> { Seq::empty() });
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

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).2 == Seq::empty()
            && I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    // Creusot's `produces`: the inner items `s`, the closure states `fs` with `fs[k]` before and
    // `fs[k + 1]` after the `k`-th call (Creusot's `fs: Seq<&mut F>` read as `*fs[k]` and
    // `^fs[k]`), and the history `produced ++ s[..k]` at the `k`-th call.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && exists(|s: Seq<A>| exists(|fs: Seq<Closure<F>>|
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
}

// `slice::Iter<u32>` as an iterator of the local spec; `next` is std's, through its extern spec,
// and the predicates are std.rs's `IteratorSpec` ones for it.
#[thrust_macros::context]
impl<'a> Iterator for core::slice::Iter<'a, u32> {
    type Item = &'a u32;

    fn next(&mut self) -> Option<&'a u32> {
        std::iter::Iterator::next(self)
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        <Self as IteratorSpec>::inv(self)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        <Self as IteratorSpec>::completed(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        <Self as IteratorSpec>::produces(self, visited, o)
    }
}

#[thrust_macros::context]
#[thrust::callable]
pub fn counter(v: Vec<u32>) {
    let mut cnt: usize = 0;
    // Creusot's closure (line 46) has no written contract: Creusot takes it from the body
    // (`[@coma:extspec]` in `03_std_iterators.coma`), where its `proof_assert!` states the history
    // fact `cnt == produced.len()`. Here that fact is the closure's precondition, written: Thrust
    // infers a closure's precondition only from callers it analyzes, and `collect` is trusted. It
    // is also a postcondition on the entry state, which gives the caller `cnt == x.len()`.
    let x: Vec<u32> = v
        .iter()
        .map_inv(thrust_macros::closure!(
            captures(cnt: &mut &mut usize),
            requires(*(*cnt) == produced.len()),
            ensures(*(!cnt) == *(*cnt) + 1 && result == *x),
            ensures(*(*cnt) == produced.len()),
            |x: &u32, produced: Ghost<Seq<&U32>>| -> u32 {
                cnt += 1;
                *x
            }))
        .collect();

    thrust_macros::proof_assert!(|x: Vec<u32>, v: Vec<u32>| x.len() == v.len());
    thrust_macros::proof_assert!(|x: Vec<u32>, v: Vec<u32>| x == v);
    // Unsat: the closure ran once per item.
    thrust_macros::proof_assert!(|cnt: usize, x: Vec<u32>| cnt == x.len() + 1);
}
