//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
use thrust_models::model::{Closure, Int, Mut, Seq, UInt};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `examples/counter` with its own property: `v.iter().map_inv(|x, _prod| { cnt += 1; *x })
// .collect()`, then `x == v` and `cnt == x.len()`. The source is a `Range` instead of `v.iter()`,
// so `x == v` reads `x` is the range's sequence. `Map` is Creusot's `MapInv`
// (`iterators/map_ext.rs`) with an `FnMut` closure: `produces` carries the chain `fs` of closure
// states, `preservation_inv` and `reinitialize` quantify over every closure state, as Creusot's
// do. As in creusot-std's `std/iter/map_inv.rs`, which `examples/counter` uses, `produces` relates
// the first state to the last and to every state of the chain by `unnest!` (Creusot's
// `hist_inv`), and `preservation_inv` is guarded by it. The closure precondition drops Creusot's
// `cnt < usize::MAX` (integers are unbounded).
//
// `Map`'s specification uses `unnest!`, so its methods are verified once over `F`, and `collect`
// at `Map<Range, closure>` uses its generic analysis with the closure's `unnest!` laws checked.
// `unnest!` gives the final state the prophecy of the borrow of `cnt`, the last call's
// postcondition its value, and `produces_trans` is proved by lemmas that name the joined
// witnesses as terms (Creusot's session gives them by hand, `exists (s1 ++ s)` and
// `exists (fs1 ++ fs)`).

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

    // Creusot's `collect` (iter.rs): `exists done prod. resolve(^done) && done.completed()
    // && self.produces(prod, *done) && B::from_iter_post(prod, result)`, with `from_iter_post`
    // for `Vec` (vec.rs) `prod == res@` folded in: `result` is the produced sequence. `&mut self`
    // as in `decuple_range.rs`: the caller keeps the adapter, whose drop resolves the closure's
    // borrow of `cnt`.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty|
        Self::produces(*self, result, pre) && Self::completed(Mut::new(pre, !self))))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized,
        <Self as Model>::Ty: PartialEq,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        B::from_iter(self)
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

    // `next`'s singleton `produces`, from the inner item `e` the call consumed (Creusot's
    // `produces_one`).
    #[thrust_macros::requires(I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!(Mut::new(s0.1, s1.1)(e, s0.2), b))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(s0, Seq::singleton(b), s1))]
    fn produces_one_produces(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {}

    // `produces_trans` on ghost arguments: `produces_at` of the joined witnesses, then the
    // introduction of `produces`'s existentials at them.
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
        Self::produces_trans_at(a, ab, b, bc, c);
        Self::produces_join_intro(a, ab, b, bc, c);
    }

    // `produces`'s existentials introduced at the joined witnesses, the chain's and then the input
    // sequence's.
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
        Self::produces_join_inputs(a, ab, b, bc, c);
    }

    // The input sequence's existential introduced at `sab ++ sbc`.
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

    // `produces_at` of the joined witnesses, with the witnesses of the two halves' `exists`
    // universally quantified: the input sequences concatenated (the session's `exists (s1 ++ s)`)
    // and the closure chains joined at their shared state `b.func`, `fab[..ab.len()] ++ fbc` (the
    // session's `exists (fs1 ++ fs)`; Thrust's chain holds the states, one more than Creusot's
    // `&mut F` steps, so the shared one is dropped once).
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
        Self::history_join(a, ab, bc);
    }

    // The joined input sequence read at `k` and its history, below `ab.len()` in the first half and
    // from it on in the second (the session's `instantiate H2 (i - length ab)`).
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>| forall(|k: Int|
        !(sab.len() == ab.len() && 0 <= k && k < ab.len())
            || (sab.concat(sbc)[k] == sab[k]
                && a.2.concat(sab.concat(sbc).subsequence(0, k)) == a.2.concat(sab.subsequence(0, k)))))))]
    #[thrust_macros::ensures(forall(|sab: Seq<A>| forall(|sbc: Seq<A>| forall(|k: Int|
        !(sab.len() == ab.len() && sbc.len() == bc.len() && ab.len() <= k && k < ab.len() + bc.len())
            || (sab.concat(sbc)[k] == sbc[k - ab.len()]
                && a.2.concat(sab.concat(sbc).subsequence(0, k)) == a.2.concat(sab).concat(sbc.subsequence(0, k - ab.len())))))))]
    fn history_join(a: Ghost<Self>, ab: Ghost<Seq<<B as Model>::Ty>>, bc: Ghost<Seq<<B as Model>::Ty>>) {}
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
                    thrust_macros::ghost!(|self: &mut Self, e: Ghost<<I as Iterator>::Item>| -> Seq<A> { (*self).2.push(e) });
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                Self::produces_one_produces(pre, e, bm, post);
                Some(b)
            }
            None => {
                self.produced = thrust_macros::ghost!(|| -> Seq<A> { Seq::empty() });
                None
            }
        }
    }


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
    start: u32,
    end: u32,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
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

// `FromIterator<A>` reduced to `from_iter`; `Self: Model<Ty = Seq<..>>` lets `result` feed `produces`.
#[thrust_macros::context]
trait FromIterator<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(*iter))]
    #[thrust_macros::ensures(exists(|pre: <I as Model>::Ty|
        I::produces(*iter, result, pre) && I::completed(Mut::new(pre, !iter))))]
    fn from_iter<I: Iterator<Item = A> + Model>(iter: &mut I) -> Self
    where
        <I as Model>::Ty: PartialEq;
}

#[thrust_macros::context]
impl FromIterator<u32> for Vec<u32> {
    fn from_iter<I: Iterator<Item = u32> + Model>(iter: &mut I) -> Vec<u32>
    where
        <I as Model>::Ty: PartialEq,
    {
        let it = iter;
        let mut v: Vec<u32> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<u32>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry() && I::invariant(*it) && I::produces(*iter.at_entry(), v, *it)
            );
            v.push(x);
        }
        v
    }
}

// Creusot: `proof_assert! { (@x).ext_eq(@v) }; proof_assert! { @cnt == (@x).len() }`, with the
// range `start..end` for `v`.
#[thrust_macros::requires(start <= end)]
#[thrust_macros::ensures(result.0.len() == end - start
    && forall(|k: Int| 0 <= k && k < result.0.len() ==> result.0[k] == start + k)
    && result.1 == result.0.len())]
fn counter(start: u32, end: u32) -> (Vec<u32>, usize) {
    let mut cnt: usize = 0;
    let f = thrust_macros::closure!(
        captures(cnt: &mut &mut usize),
        requires(*(*cnt) == produced.len()),
        ensures(*(!cnt) == *(*cnt) + 1 && result == x),
        // The precondition restated, as in the postcondition Creusot infers for the closure
        // body, which reads `cnt == produced.len()` before the increment.
        ensures(*(*cnt) == produced.len()),
        // Creusot's `postcondition_mut` of a closure adds `unnest(*self, ^self)`, for this
        // capture that the borrow of `cnt` keeps its prophecy.
        ensures(!(!cnt) == !(*cnt)),
        |x: u32, produced: Ghost<Seq<UInt>>| -> u32 { cnt += 1; x },
    );
    let mut m = Map {
        iter: Range { start, end },
        func: f,
        produced: thrust_macros::ghost!(|| -> Seq<UInt> { Seq::empty() }),
    };
    let x = m.collect::<Vec<u32>>();
    (x, cnt)
}

fn main() {}
