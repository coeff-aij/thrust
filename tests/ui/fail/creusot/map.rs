//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Fail twin of `decuple_range_lemmas.rs`, for `Map::produces` rather than for `Range::produces`
// (`fail/decuple_range_lemmas.rs`): `Map::produces` relates every `visited[k]` to the first inner
// item `s[0]` instead of `s[k]`. `fail/map_creusot_lemmas.rs` makes the same change but its call
// site (`map_creusot.rs`'s two direct `next()`s) only ever checks a singleton `produces`, where
// `s[0] == s[k]` trivially (k = 0), so the change refutes nothing there within 120 s (triaged in
// experiments/2026-09-27-map-fail-twin-triage.md). `decuple_range()`'s `collect` loop invariant
// and its `ensures(result[k] == k * 10)` force `Map::produces` concretely, at a length-10 sequence
// of distinct values, so the same change is refutable here.
//
// Creusot's `examples/decuple_range` with its positional property `v[i] == 10 * i`, fully checked,
// with `Map` in its `produces` form over an `FnMut` closure, as `../../pass/creusot/map.rs`. The
// rest is `collect` and `FromIterator for Vec<i64>`, as in `weaker/collect_mutref.rs`.

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

    // Creusot's `collect` (iter.rs): `exists done prod. resolve(^done) && done.completed()
    // && self.produces(prod, *done) && B::from_iter_post(prod, result)`, with `from_iter_post`
    // for `Vec` (vec.rs) `prod == res@` folded in: `result` is the produced sequence. `&mut self`
    // as in `creusot/weaker/collect_mutref.rs`.
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

struct Map<I, F> {
    iter: I,
    func: F,
}

// The model is the tuple (iter, func), read as `.0`, `.1` in the specifications.
impl<I: Model, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I, A, B, F> Map<I, F>
where
    I: Iterator + Model,
    A: Model<Ty = A> + PartialEq,
    B: Model,
    F: FnMut(I::Item) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: A| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    // Creusot's `preservation_inv` (and `preservation`), over every closure state `f1` that `func`
    // reaches (`func.hist_inv(*f)`) and its successor `f2` (Creusot's `f: &mut F`).
    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F) -> bool {
        forall(|s: Seq<A>|
        forall(|e1: A|
        forall(|e2: A|
        forall(|i: <I as Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as Model>::Ty|
            !(thrust_macros::unnest!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(f1(e1))
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    // Creusot's `reinitialize`: after completion, the next item's precondition and preservation
    // hold again, for every closure state.
    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f)
                    && Self::preservation_inv(fin, f)))))
    }

    // Creusot's `produces_one`: one closure call from `s0.func` to `s1.func` (Creusot's
    // `f: &mut F` with `*f == self.func && ^f == succ.func`), one inner item `e` mapped to
    // `visited`.
    #[thrust_macros::predicate]
    fn produces_one(s0: Self, visited: B, s1: Self) -> bool {
        exists(|e: A|
            I::produces(s0.0, Seq::singleton(e), s1.0)
                && thrust_macros::post!(Mut::new(s0.1, s1.1)(e), visited))
    }

    // `produces` with its input sequence `s` and closure chain `fs` given: the body of `produces`
    // under its `exists`.
    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Seq<<B as Model>::Ty>, o: Self, s: Seq<A>, fs: Seq<F>) -> bool {
        thrust_macros::unnest!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::unnest!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[0]), visited[k])))
    }

    // `produces` with its input sequence `s` given: `produces_at` under the `exists` of the chain.
    #[thrust_macros::predicate]
    fn produces_with(s0: Self, visited: Seq<<B as Model>::Ty>, o: Self, s: Seq<A>) -> bool {
        exists(|fs: Seq<Closure<F>>| Self::produces_at(s0, visited, o, s, fs))
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
    }

    // `produces_at` of the joined witnesses.
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
    }
}

#[thrust_macros::context]
impl<I, A, B, F> Iterator for Map<I, F>
where
    I: Iterator + Model,
    A: Model<Ty = A> + PartialEq,
    B: Model,
    F: FnMut(I::Item) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    type Item = B;

    fn next(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v);
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                // Keeps `self` live at the snapshot `post`, as the history update does in
                // `counter_creusot.rs`.
                let _keep = &*self;
                Some(b)
            }
            None => None,
        }
    }

    fn produces_refl(a: &Map<I, F>) {}

    fn produces_trans(a: &Map<I, F>, ab: Seq<<Self::Item as Model>::Ty>, b: &Map<I, F>, bc: Seq<<Self::Item as Model>::Ty>, c: &Map<I, F>) {
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
            && Self::preservation_inv(self.0, self.1)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    // Creusot's `produces`: the inner items `s`, the closure states `fs` with `fs[k]` before and
    // `fs[k + 1]` after the `k`-th call (Creusot's `fs: Seq<&mut F>` read as `*fs[k]` and
    // `^fs[k]`).
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        thrust_macros::unnest!(self.1, o.1)
            && exists(|s: Seq<A>| exists(|fs: Seq<Closure<F>>|
            s.len() == visited.len()
                && I::produces(self.0, s, o.0)
                && fs.len() == visited.len() + 1
                && fs[0] == self.1
                && fs[visited.len()] == o.1
                && forall(|k: Int|
                    !(0 <= k && k < visited.len())
                        || (thrust_macros::unnest!(self.1, fs[k])
                            && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[0]), visited[k])))))
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
impl FromIterator<i64> for Vec<i64> {
    fn from_iter<I: Iterator<Item = i64> + Model>(iter: &mut I) -> Vec<i64>
    where
        <I as Model>::Ty: PartialEq,
    {
        let it = iter;
        let mut v: Vec<i64> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<i64>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry() && I::invariant(*it) && I::produces(*iter.at_entry(), v, *it)
            );
            v.push(x);
        }
        v
    }
}

// Creusot: `proof_assert! { forall<i : Int> 0 <= i && i < (@v).len() ==> @(@v)[i] == i * 10 }`.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> result[k] == k * 10))]
fn decuple_range() -> Vec<i64> {
    let f = thrust_macros::closure!(
        requires(x < 100),
        ensures(result == x * 10),
        |x: i64| -> i64 { x * 10 }
    );
    let mut m = Map {
        iter: Range { start: 0, end: 10 },
        func: f,
    };
    m.collect::<Vec<i64>>()
}

fn main() {}
