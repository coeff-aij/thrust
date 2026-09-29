//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:0360cb142
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `MapInv` (`iterators/map_ext.rs` in the artifact, Why3 session
// `proofs/map_ext/why3session.xml`) in its own form: the closure receives the ghost history
// `produced` of the inner items consumed so far, so its precondition may depend on it. `produces`
// extends `produced` by the existential input sequence `s` and calls the closure at the history
// `produced ++ s[..k]` for the `k`-th item; the invariant is Creusot's `reinitialize`,
// `preservation_inv`, the inner invariant and `next_precondition`. The closure is `FnMut`, as
// Creusot's: `produces` carries the chain `fs` of closure states related by `unnest!` (Creusot's
// `unnest`, `hist_inv` in creusot-std), and `preservation_inv` and `reinitialize` quantify over
// every closure state. The adapter and its lemmas are `counter_creusot.rs`'s (lemmas called from
// ghost code in `next` and `produces_trans`).
// Fail twin: `next` does not extend `produced` by the consumed item.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, proved by each
// impl, and `next` with Creusot's contract.
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
    fn produces_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;
}

struct Map<I, A, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<A>>,
}

// The model is the tuple (iter, func, produced), read as `.0`, `.1`, `.2` in the specifications.
// A struct model would need `PartialEq` on `Map`, whose derived `eq` compares the `Ghost` field in
// executable code, which Thrust rejects.
impl<I: Model, A, F> Model for Map<I, A, F> {
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<A>);
}

#[thrust_macros::context]
impl<I, A, B, F> Map<I, A, F>
where
    I: Iterator + Model,
    A: Model<Ty = A> + PartialEq,
    B: Model,
    F: FnMut(I::Item, Ghost<Seq<A>>) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
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
            !(thrust_macros::unnest!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(f1(e1, produced.concat(s)))
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

    // Creusot's `produces_one`: one closure call from `s0.func` to `s1.func` (Creusot's
    // `f: &mut F` with `*f == self.func && ^f == succ.func`), one inner item `e` mapped to `visited`
    // at the history `produced`, and `produced` extended by `e`.
    #[thrust_macros::predicate]
    fn produces_one(s0: Self, visited: B, s1: Self) -> bool {
        exists(|e: A|
            I::produces(s0.0, Seq::singleton(e), s1.0)
                && s1.2 == s0.2.push(e)
                && thrust_macros::post!(Mut::new(s0.1, s1.1)(e, s0.2), visited))
    }

    // `produces` with its input sequence `s` and closure chain `fs` given: the body of `produces`
    // under its `exists`.
    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Seq<<B as Model>::Ty>, o: Self, s: Seq<A>, fs: Seq<F>) -> bool {
        thrust_macros::unnest!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && o.2 == s0.2.concat(s)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::unnest!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k], s0.2.concat(s.subsequence(0, k))), visited[k])))
    }

    // `produces` with its input sequence `s` given: `produces_at` under the `exists` of the chain.
    #[thrust_macros::predicate]
    fn produces_with(s0: Self, visited: Seq<<B as Model>::Ty>, o: Self, s: Seq<A>) -> bool {
        exists(|fs: Seq<Closure<F>>| Self::produces_at(s0, visited, o, s, fs))
    }

    // The direction of `produces_one`'s ensures that `next` uses, with the witnesses `[e]` and
    // `[s0.func, s1.func]` as terms.
    #[thrust_macros::requires(I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!(Mut::new(s0.1, s1.1)(e, s0.2), b))]
    #[thrust_macros::ensures(Self::produces_one(s0, b, s1))]
    #[thrust_macros::ensures(Self::produces_at(s0, Seq::singleton(b), s1, Seq::singleton(e), Seq::singleton(s0.1).push(s1.1)))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(s0, Seq::singleton(b), s1))]
    fn produces_one_produces(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {}

    // One lemma per conjunct of the invariant (the session's `split_vc`), each taking the inner
    // item `e` that `produces_one`'s `exists` hides.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!(Mut::new(s0.1, s1.1)(e, s0.2), b)
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(Self::next_precondition(s1.0, s1.1, s1.2))]
    fn produces_one_next_precondition(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {}

    // The instance of `preservation_inv(s0)` that `preservation_inv(s1)` needs, at the prefix
    // `t = [e] ++ s` (the session's instantiation), with the history identity
    // `s0.produced ++ t == s1.produced ++ s` stated beside it.
    #[thrust_macros::requires(I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e))]
    #[thrust_macros::ensures(forall(|s: Seq<A>|
        forall(|e1: A|
        forall(|e2: A|
        forall(|i: <I as Model>::Ty|
            !I::produces(s1.0, s.push(e1).push(e2), i)
                || exists(|t: Seq<A>|
                    t == Seq::singleton(e).concat(s)
                        && s0.2.concat(t) == s1.2.concat(s)
                        && I::produces(s0.0, t.push(e1).push(e2), i)))))))]
    fn produces_one_prefix(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, s1: Ghost<Self>) {}

    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::unnest!(s0.1, s1.1)
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(Self::preservation_inv(s1.0, s1.1, s1.2))]
    fn produces_one_preservation(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, s1: Ghost<Self>) {
        Self::produces_one_prefix(s0, e, s1);
    }

    // Creusot's `produces_one_invariant`, with the inner item `e` as an argument. `reinitialize`
    // does not depend on the state, so it carries over from `s0`.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && Self::produces_one(s0, b, s1)
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!(Mut::new(s0.1, s1.1)(e, s0.2), b)
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(<Self as Iterator>::invariant(s1))]
    fn produces_one_invariant(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {
        Self::produces_one_next_precondition(s0, e, b, s1);
        Self::produces_one_preservation(s0, e, s1);
    }

    // `produces_trans` on ghost arguments.
    #[thrust_macros::requires(<Self as Iterator>::produces(a, ab, b)
        && <Self as Iterator>::produces(b, bc, c))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(a, ab.concat(bc), c))]
    fn produces_trans_split(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::produces_trans_witness(a, ab, b, bc, c);
    }

    // The existential introduction of `produces(a, ab.concat(bc), c)`, with the witnesses of the two halves'
    // `exists` universally quantified and the joined witnesses as terms: the input sequences
    // concatenated (the session's `exists (s1 ++ s)`) and the closure chains joined at their shared
    // state `b.func`, `fab[..ab.len()] ++ fbc` (the session's `exists (fs1 ++ fs)`; Thrust's chain
    // holds the states, one more than Creusot's `&mut F` steps, so the shared one is dropped once).
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || <Self as Iterator>::produces(a, ab.concat(bc), c))))))]
    fn produces_trans_witness(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::produces_trans_at(a, ab, b, bc, c);
        Self::produces_join_intro(a, ab, b, bc, c);
    }

    // `produces`'s existential introduced at the joined witnesses, over the same variables as
    // `produces_trans_at`'s conclusion.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc))
            || <Self as Iterator>::produces(a, ab.concat(bc), c))))))]
    fn produces_join_intro(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::produces_join_chain(a, ab, b, bc, c);
        Self::produces_join_inputs(a, ab, b, bc, c);
    }

    // `produces`'s two existentials introduced one at a time at the joined witnesses, over the same
    // variables as `produces_trans_at`'s conclusion: first the closure chain, then the input
    // sequence.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc))
            || Self::produces_with(a, ab.concat(bc), c, sab.concat(sbc)))))))]
    fn produces_join_chain(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        !Self::produces_with(a, ab.concat(bc), c, sab.concat(sbc)) || <Self as Iterator>::produces(a, ab.concat(bc), c))))]
    fn produces_join_inputs(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // `produces_at` of the joined witnesses: one lemma per group of conjuncts (the session's
    // `split_vc`).
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::trans_inputs(a, ab, b, bc, c);
        Self::trans_ends(a, ab, b, bc, c);
        Self::trans_calls(a, ab, b, bc, c);
    }

    // The input sequence, the inner `produces` and the history of the joined witness.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || (sab.concat(sbc).len() == ab.concat(bc).len()
                && I::produces(a.0, sab.concat(sbc), c.0)
                && c.2 == a.2.concat(sab.concat(sbc))))))))]
    fn trans_inputs(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // The first and the last closure state and the length of the joined chain, and `unnest!` from
    // the first to the last state.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || (thrust_macros::unnest!(a.1, c.1)
                && fab.subsequence(0, ab.len()).concat(fbc).len() == ab.concat(bc).len() + 1
                && fab.subsequence(0, ab.len()).concat(fbc)[0] == a.1
                && fab.subsequence(0, ab.len()).concat(fbc)[ab.concat(bc).len()] == c.1))))))]
    fn trans_ends(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // Every call of the joined witnesses, in the form of `produces_at`'s last conjunct: the two
    // halves below and from `ab.len()`.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || forall(|k: Int|
                !(0 <= k && k < ab.concat(bc).len())
                    || (thrust_macros::unnest!(a.1, fab.subsequence(0, ab.len()).concat(fbc)[k])
                        && thrust_macros::post!(Mut::new(fab.subsequence(0, ab.len()).concat(fbc)[k], fab.subsequence(0, ab.len()).concat(fbc)[k + 1])(
                            sab.concat(sbc)[k], a.2.concat(sab.concat(sbc).subsequence(0, k))), ab.concat(bc)[k]))))))))]
    fn trans_calls(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::trans_lower(a, ab, b, bc, c);
        Self::trans_upper(a, ab, b, bc, c);
    }

    // The calls of the first half, below `ab.len()`.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>| forall(|k: Int|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc)
            && 0 <= k && k < ab.len())
            || (thrust_macros::unnest!(a.1, fab.subsequence(0, ab.len()).concat(fbc)[k])
                && thrust_macros::post!(Mut::new(fab.subsequence(0, ab.len()).concat(fbc)[k], fab.subsequence(0, ab.len()).concat(fbc)[k + 1])(
                    sab.concat(sbc)[k], a.2.concat(sab.concat(sbc).subsequence(0, k))), ab.concat(bc)[k]))))))))]
    fn trans_lower(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::join_lower_visited(ab, bc);
        Self::join_lower_inputs(a, ab);
        Self::join_lower_chain(ab, b, bc);
    }

    // The calls of the second half, from `ab.len()` on, at `k - ab.len()` in `bc`.
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>| forall(|k: Int|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc)
            && ab.len() <= k && k < ab.concat(bc).len())
            || (thrust_macros::unnest!(a.1, fab.subsequence(0, ab.len()).concat(fbc)[k])
                && thrust_macros::post!(Mut::new(fab.subsequence(0, ab.len()).concat(fbc)[k], fab.subsequence(0, ab.len()).concat(fbc)[k + 1])(
                    sab.concat(sbc)[k], a.2.concat(sab.concat(sbc).subsequence(0, k))), ab.concat(bc)[k]))))))))]
    fn trans_upper(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::join_upper_visited(ab, bc);
        Self::join_upper_inputs(a, ab, bc);
        Self::join_upper_chain(ab, bc);
    }

    // The joined witnesses read at `k`, one lemma per sequence and side: below `ab.len()` the first
    // half at `k`, from `ab.len()` on the second half at `k - ab.len()`.
    #[thrust_macros::ensures(forall(|k: Int|
        !(0 <= k && k < ab.len()) || ab.concat(bc)[k] == ab[k]))]
    fn join_lower_visited(ab: Ghost<Seq<<B as Model>::Ty>>, bc: Ghost<Seq<<B as Model>::Ty>>) {}

    #[thrust_macros::ensures(forall(|k: Int|
        !(ab.len() <= k && k < ab.len() + bc.len()) || ab.concat(bc)[k] == bc[k - ab.len()]))]
    fn join_upper_visited(ab: Ghost<Seq<<B as Model>::Ty>>, bc: Ghost<Seq<<B as Model>::Ty>>) {}

    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>| forall(|k: Int|
        !(sab.len() == ab.len() && 0 <= k && k < ab.len())
            || (sab.concat(sbc)[k] == sab[k]
                && a.2.concat(sab.concat(sbc).subsequence(0, k)) == a.2.concat(sab.subsequence(0, k)))))))]
    fn join_lower_inputs(a: Ghost<Self>, ab: Ghost<Seq<<B as Model>::Ty>>) {
    }

    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>| forall(|k: Int|
        !(sab.len() == ab.len() && sbc.len() == bc.len() && ab.len() <= k && k < ab.len() + bc.len())
            || (sab.concat(sbc)[k] == sbc[k - ab.len()]
                && a.2.concat(sab.concat(sbc).subsequence(0, k)) == a.2.concat(sab).concat(sbc.subsequence(0, k - ab.len())))))))]
    fn join_upper_inputs(a: Ghost<Self>, ab: Ghost<Seq<<B as Model>::Ty>>, bc: Ghost<Seq<<B as Model>::Ty>>) {
    }

    #[thrust_macros::ensures(forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>| forall(|k: Int|
        !(fab.len() == ab.len() + 1 && fbc.len() == bc.len() + 1
            && fab[ab.len()] == b.1 && fbc[0] == b.1 && 0 <= k && k < ab.len())
            || (fab.subsequence(0, ab.len()).concat(fbc)[k] == fab[k]
                && fab.subsequence(0, ab.len()).concat(fbc)[k + 1] == fab[k + 1])))))]
    fn join_lower_chain(ab: Ghost<Seq<<B as Model>::Ty>>, b: Ghost<Self>, bc: Ghost<Seq<<B as Model>::Ty>>) {
    }

    #[thrust_macros::ensures(forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>| forall(|k: Int|
        !(fab.len() == ab.len() + 1 && fbc.len() == bc.len() + 1 && ab.len() <= k && k < ab.len() + bc.len())
            || (fab.subsequence(0, ab.len()).concat(fbc)[k] == fbc[k - ab.len()]
                && fab.subsequence(0, ab.len()).concat(fbc)[k + 1] == fbc[k - ab.len() + 1])))))]
    fn join_upper_chain(ab: Ghost<Seq<<B as Model>::Ty>>, bc: Ghost<Seq<<B as Model>::Ty>>) {
    }
}

#[thrust_macros::context]
impl<I, A, B, F> Iterator for Map<I, A, F>
where
    I: Iterator + Model,
    A: Model<Ty = A> + PartialEq,
    B: Model,
    F: FnMut(I::Item, Ghost<Seq<A>>) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    type Item = B;

    // Creusot's `next`: the closure is called with the history before `v`, then `v` is pushed;
    // on `None` the history is reset.
    fn next(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v, self.produced);
                self.produced =
                    thrust_macros::ghost!(|self: &mut Self, e: Ghost<<I as Iterator>::Item>| -> Seq<A> { (*self).2 });
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                Self::produces_one_produces(pre, e, bm, post);
                Self::produces_one_invariant(pre, e, bm, post);
                Some(b)
            }
            None => {
                self.produced = thrust_macros::ghost!(|| -> Seq<A> { Seq::empty() });
                None
            }
        }
    }

    fn produces_refl(a: &Map<I, A, F>) {}

    fn produces_trans(a: &Map<I, A, F>, ab: Seq<<Self::Item as Model>::Ty>, b: &Map<I, A, F>, bc: Seq<<Self::Item as Model>::Ty>, c: &Map<I, A, F>) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<B as Model>::Ty>| -> Seq<<B as Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<B as Model>::Ty>| -> Seq<<B as Model>::Ty> { bc });
        Self::produces_trans_split(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
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
        thrust_macros::unnest!(self.1, o.1)
            && exists(|s: Seq<A>| exists(|fs: Seq<Closure<F>>|
            s.len() == visited.len()
                && I::produces(self.0, s, o.0)
                && o.2 == self.2.concat(s)
                && fs.len() == visited.len() + 1
                && fs[0] == self.1
                && fs[visited.len()] == o.1
                && forall(|k: Int|
                    !(0 <= k && k < visited.len())
                        || (thrust_macros::unnest!(self.1, fs[k])
                            && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k], self.2.concat(s.subsequence(0, k))), visited[k])))))
    }
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }

    fn produces_refl(a: &Range) {}

    fn produces_trans(a: &Range, ab: Seq<<Self::Item as Model>::Ty>, b: &Range, bc: Seq<<Self::Item as Model>::Ty>, c: &Range) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

fn main() {
    // The precondition depends on the history: the k-th item is k + 1.
    let f = thrust_macros::closure!(
        requires(x == produced.len() + 1),
        ensures(result == x * 10),
        |x: i64, produced: Ghost<Seq<Int>>| -> i64 { x * 10 }
    );
    let mut m = Map {
        iter: Range { start: 1, end: 5 },
        func: f,
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    let first = m.next();
    let second = m.next();
    assert!(matches!(first, Some(10)));
    assert!(matches!(second, Some(20)));
}
