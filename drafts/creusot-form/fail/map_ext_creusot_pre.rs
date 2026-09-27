use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `MapInv` (`iterators/map_ext.rs` in the artifact, Why3 session
// `proofs/map_ext/why3session.xml`) in its own form: the closure receives the ghost history
// `produced` of the inner items consumed so far, so its precondition may depend on it. `produces`
// extends `produced` by the existential input sequence `s` and calls the closure at the history
// `produced ++ s[..k]` for the `k`-th item; the invariant is Creusot's `reinitialize`,
// `preservation_inv`, the inner invariant and `next_precondition`. The proof structure is the one
// of `map_creusot_lemmas.rs` (lemmas called from ghost code in `next` and `produces_trans`).
// Fail twin: the closure's precondition holds for the first item only (`x == 1`), so
// `preservation_inv` fails at the call site.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
    <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity as a callable law: an adapter that answers without touching its inner
    // iterator (`Take` at `n == 0`) has no `next` ensures of the inner to take it from.
    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    // Creusot's `produces_trans` in its concatenation form, as a law.
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b) && Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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
    F: Fn(I::Item, Ghost<Seq<A>>) -> B,
    <I as Iterator>::Item: Model<Ty = A>,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    // Creusot's `next_precondition`: forall e i. iter.produces([e], i) ==> pre(func(e, produced))
    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F, produced: Seq<A>) -> bool {
        forall(|e: A| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e, produced))))
    }

    // Creusot's `preservation_inv` (and, at `produced == []`, `preservation`):
    // forall s e1 e2 i b. iter.produces(s.push(e1).push(e2), i)
    //   && pre(func(e1, produced ++ s)) && post(func(e1, produced ++ s), b)
    //   ==> pre(func(e2, (produced ++ s).push(e1)))
    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F, produced: Seq<A>) -> bool {
        forall(|s: Seq<A>|
        forall(|e1: A|
        forall(|e2: A|
        forall(|i: <I as Model>::Ty|
        forall(|b: <B as Model>::Ty|
            !(I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(func(e1, produced.concat(s)))
                && thrust_macros::post!(func(e1, produced.concat(s)), b))
                || thrust_macros::pre!(func(e2, produced.concat(s).push(e1))))))))
    }

    // Creusot's `reinitialize`: after completion (`produced` reset to []), the next item's
    // precondition and preservation hold again.
    #[thrust_macros::predicate]
    fn reinitialize(func: F) -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, func, Seq::empty())
                    && Self::preservation_inv(fin, func, Seq::empty()))))
    }

    // Creusot's `produces_one`: `func` unchanged, one inner item `e` mapped to `visited` at the
    // history `produced`, and `produced` extended by `e`.
    #[thrust_macros::predicate]
    fn produces_one(s0: Self, visited: B, s1: Self) -> bool {
        s0.1 == s1.1
            && exists(|e: A|
                I::produces(s0.0, Seq::singleton(e), s1.0)
                    && s1.2 == s0.2.push(e)
                    && thrust_macros::post!((s0.1)(e, s0.2), visited))
    }

    // The direction of `produces_one`'s ensures that `next` uses, with the witness `[e]` as a term.
    #[thrust_macros::requires(s0.1 == s1.1
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!((s0.1)(e, s0.2), b))]
    #[thrust_macros::ensures(Self::produces_one(s0, b, s1))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(s0, Seq::singleton(b), s1))]
    fn produces_one_produces(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {}

    // One lemma per conjunct of the invariant (the session's `split_vc`), each taking the inner
    // item `e` that `produces_one`'s `exists` hides.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && s0.1 == s1.1
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!((s0.1)(e, s0.2), b)
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
        && s0.1 == s1.1
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!((s0.1)(e, s0.2), b)
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(Self::preservation_inv(s1.0, s1.1, s1.2))]
    fn produces_one_preservation(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {
        Self::produces_one_prefix(s0, e, s1);
    }

    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && s0.1 == s1.1
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(Self::reinitialize(s1.1))]
    fn produces_one_reinitialize(s0: Ghost<Self>, s1: Ghost<Self>) {}

    // Creusot's `produces_one_invariant`, with the inner item `e` as an argument.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && Self::produces_one(s0, b, s1)
        && I::produces(s0.0, Seq::singleton(e), s1.0)
        && s1.2 == s0.2.push(e)
        && thrust_macros::post!((s0.1)(e, s0.2), b)
        && I::invariant(s1.0))]
    #[thrust_macros::ensures(<Self as Iterator>::invariant(s1))]
    fn produces_one_invariant(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {
        Self::produces_one_next_precondition(s0, e, b, s1);
        Self::produces_one_preservation(s0, e, b, s1);
        Self::produces_one_reinitialize(s0, s1);
    }

    // `produces_trans` with the concatenation of the visited sequences spelled out index by index.
    #[thrust_macros::requires(<Self as Iterator>::produces(a, ab, b)
        && <Self as Iterator>::produces(b, bc, c))]
    #[thrust_macros::ensures(forall(|v: Seq<<B as Model>::Ty>|
        !(v.len() == ab.len() + bc.len()
            && forall(|k: Int| !(0 <= k && k < ab.len()) || v[k] == ab[k])
            && forall(|k: Int| !(ab.len() <= k && k < v.len()) || v[k] == bc[k - ab.len()]))
            || <Self as Iterator>::produces(a, v, c)))]
    fn produces_trans_split(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }
}

#[thrust_macros::context]
impl<I, A, B, F> Iterator for Map<I, A, F>
where
    I: Iterator + Model,
    A: Model<Ty = A> + PartialEq,
    B: Model,
    F: Fn(I::Item, Ghost<Seq<A>>) -> B,
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

    // Creusot's `invariant`: reinitialize && preservation_inv && iter.invariant && next_precondition
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize(self.1)
            && Self::preservation_inv(self.0, self.1, self.2)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1, self.2)
    }

    // Creusot's `completed`: the history is reset, the inner iterator completed, `func` unchanged.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).2 == Seq::empty()
            && I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    // self.func == o.func && exists s. s.len() == visited.len() && iter.produces(s, o.iter)
    //   && o.produced == self.produced ++ s
    //   && forall k. 0 <= k < visited.len() ==> post(func(s[k], self.produced ++ s[0..k]), visited[k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.1 == o.1
            && exists(|s: Seq<A>|
                s.len() == visited.len()
                    && I::produces(self.0, s, o.0)
                    && o.2 == self.2.concat(s)
                    && forall(|k: Int|
                        !(0 <= k && k < visited.len())
                            || thrust_macros::post!((self.1)(s[k], self.2.concat(s.subsequence(0, k))), visited[k])))
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
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.resolve() && self.start >= self.end
        "(and
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
            (>= (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_)))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        // self.end == o.end && self.start <= o.start
        // && (visited.len() > 0 ==> o.start <= o.end)
        // && visited.len() == o.start - self.start
        // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
        "(and
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 o))
            (<= (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.0 o))
            (=> (> (seq.len visited) 0)
                (<= (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.1 o)))
            (= (seq.len visited)
               (- (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.0 self_)))
            (forall ((zi Int))
                (=> (and (<= 0 zi) (< zi (seq.len visited)))
                    (= (seq.nth visited zi)
                       (+ (tuple_proj<Int-Int>.0 self_) zi))))
        )";
        true
    }
}


fn main() {
    // The precondition depends on the history: the k-th item is k + 1.
    let f = thrust_macros::closure!(
        requires(x == 1),
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
