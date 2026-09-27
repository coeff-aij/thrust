//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:63e7b97e4

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `examples/decuple_range` with its positional property `v[i] == 10 * i`, fully checked,
// with `Map` carrying Creusot's own proof structure (the artifact's `iterators/map.rs` and its Why3
// session `proofs/map/why3session.xml`): the predicate `produces_one` and the ghost lemmas
// `produces_one_produces` (the direction of `produces_one`'s ensures that `next` uses) and
// `produces_one_invariant`, both called from `next` on ghost snapshots taken around the inner
// `next`, as Creusot's `next` calls `produces_one_invariant` through `ghost!`. The session's manual
// steps become lemmas: `produces_one_invariant` calls one lemma per conjunct of the invariant (its
// `split_vc`) and `produces_one_prefix` (its `apply H11 with .. (singleton e ++ s)`), and the
// `produces_trans` law calls `produces_trans_split`, which states the concatenated visited sequence
// index by index. The rest is `decuple_range.rs`: `next`'s ensures are Creusot's extern spec of
// `Iterator::next`, laws `produces_refl` / `produces_trans`, and `collect` / `FromIterator for
// Vec<i64>`.
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

    // Creusot's `collect` (iter.rs): `exists done prod. resolve(^done) && done.completed()
    // && self.produces(prod, *done) && B::from_iter_post(prod, result)`, with `from_iter_post`
    // for `Vec` (vec.rs) `prod == res@` folded in: `result` is the produced sequence. `&mut self`
    // as in `traits/collect_visited_seq_mutref`.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty|
        Self::produces(*self, result, pre) && Self::completed(Mut::new(pre, !self))))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized,
        <Self as Model>::Ty: PartialEq,
    {
        B::from_iter(self)
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
}


#[derive(PartialEq)]
struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = Map<<I as Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: Iterator + Model,
    B: Model,
    F: Fn(I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    // forall e i. iter.produces([e], i) ==> pre(func(e))
    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    // forall s e1 e2 i b. iter.produces(s.push(e1).push(e2), i) && post(func(e1), b) ==> pre(func(e2))
    #[thrust_macros::predicate]
    fn preservation(iter: I, func: F) -> bool {
        forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|i: <I as Model>::Ty|
        forall(|b: <B as Model>::Ty|
            !(I::produces(iter, s.push(e1).push(e2), i) && thrust_macros::post!(func(e1), b))
                || thrust_macros::pre!(func(e2)))))))
    }

    // forall cur fin. completed(Mut(cur, fin)) ==> next_precondition(fin) && preservation(fin)
    #[thrust_macros::predicate]
    fn reinitialize(func: F) -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, func) && Self::preservation(fin, func))))
    }

    // Creusot's `produces_one`: `func` unchanged and one inner item `e` mapped to `visited`.
    #[thrust_macros::predicate]
    fn produces_one(s0: Self, visited: B, s1: Self) -> bool {
        s0.func == s1.func
            && exists(|e: <<I as Iterator>::Item as Model>::Ty|
                I::produces(s0.iter, Seq::singleton(e), s1.iter)
                    && thrust_macros::post!((s0.func)(e), visited))
    }

    // The direction of Creusot's `ensures(result == self.produces(Seq::singleton(visited), succ))`
    // on `produces_one` that `next` uses. The witness of `produces`'s `exists` is `[e]`, which
    // the session gives by hand (`exists (singleton e)`); here `e` is the lemma's argument.
    #[thrust_macros::requires(s0.func == s1.func
        && I::produces(s0.iter, Seq::singleton(e), s1.iter)
        && thrust_macros::post!((s0.func)(e), b))]
    #[thrust_macros::ensures(Self::produces_one(s0, b, s1))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(s0, Seq::singleton(b), s1))]
    fn produces_one_produces(
        s0: Ghost<Self>,
        e: Ghost<<I as Iterator>::Item>,
        b: Ghost<B>,
        s1: Ghost<Self>,
    ) {
    }

    // Creusot's `produces_one_invariant` is proved in its Why3 session by `split_vc` into the
    // invariant's conjuncts, each with its own tactic. Here each conjunct is a lemma of its own.
    // They take the inner item `e` that `produces_one`'s `exists` hides, as `next` has it: the
    // witness given as a term.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && s0.func == s1.func
        && I::produces(s0.iter, Seq::singleton(e), s1.iter)
        && thrust_macros::post!((s0.func)(e), b)
        && I::invariant(s1.iter))]
    #[thrust_macros::ensures(Self::next_precondition(s1.iter, s1.func))]
    fn produces_one_next_precondition(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {}

    // The instance of `preservation(s0.iter)` that `preservation(s1.iter)` needs, at the prefix
    // `[e] ++ s` (the session's `apply H11 with i,b,e1,(singleton e ++ s)`), named `t` so that the
    // pushed sequence keeps the shape `preservation` is stated in.
    #[thrust_macros::requires(I::produces(s0.iter, Seq::singleton(e), s1.iter))]
    #[thrust_macros::ensures(forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|i: <I as Model>::Ty|
            !I::produces(s1.iter, s.push(e1).push(e2), i)
                || exists(|t: Seq<<<I as Iterator>::Item as Model>::Ty>|
                    t == Seq::singleton(e).concat(s)
                        && I::produces(s0.iter, t.push(e1).push(e2), i)))))))]
    fn produces_one_prefix(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, s1: Ghost<Self>) {}

    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && s0.func == s1.func
        && I::produces(s0.iter, Seq::singleton(e), s1.iter)
        && thrust_macros::post!((s0.func)(e), b)
        && I::invariant(s1.iter))]
    #[thrust_macros::ensures(Self::preservation(s1.iter, s1.func))]
    fn produces_one_preservation(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {
        Self::produces_one_prefix(s0, e, s1);
    }

    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && s0.func == s1.func
        && I::invariant(s1.iter))]
    #[thrust_macros::ensures(Self::reinitialize(s1.func))]
    fn produces_one_reinitialize(s0: Ghost<Self>, s1: Ghost<Self>) {}

    // Creusot's `produces_one_invariant`, with its requires and ensures, and the inner item `e`
    // of `produces_one` as an argument.
    #[thrust_macros::requires(<Self as Iterator>::invariant(s0)
        && Self::produces_one(s0, b, s1)
        && I::produces(s0.iter, Seq::singleton(e), s1.iter)
        && thrust_macros::post!((s0.func)(e), b)
        && I::invariant(s1.iter))]
    #[thrust_macros::ensures(<Self as Iterator>::invariant(s1))]
    fn produces_one_invariant(s0: Ghost<Self>, e: Ghost<<I as Iterator>::Item>, b: Ghost<B>, s1: Ghost<Self>) {
        Self::produces_one_next_precondition(s0, e, b, s1);
        Self::produces_one_preservation(s0, e, b, s1);
        Self::produces_one_reinitialize(s0, s1);
    }

    // `produces_trans` with the concatenation of the visited sequences spelled out: any `v`
    // that is `ab` followed by `bc` index by index. With the witness `s_ab ++ s_bc` of the
    // inner sequence, the pointwise relation then reads under a concatenation on one side
    // only. `produces_trans` below instantiates `v` with `ab.concat(bc)`.
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
impl<I, B, F> Iterator for Map<I, F>
where
    I: Iterator + Model,
    B: Model,
    F: Fn(I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    type Item = B;

    // Creusot's `next`: after the inner `next` returns `Some(v)`, the closure's precondition
    // follows from `next_precondition`, and the ghost lemmas give the singleton `produces`
    // and the invariant at the next state.
    fn next(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v);
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                Self::produces_one_produces(pre, e, bm, post);
                Self::produces_one_invariant(pre, e, bm, post);
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
        I::invariant(self.iter)
            && Self::next_precondition(self.iter, self.func)
            && Self::preservation(self.iter, self.func)
            && Self::reinitialize(self.func)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    // self.func == o.func && exists s. s.len() == visited.len() && iter.produces(s, o.iter)
    //   && forall k. 0 <= k < visited.len() ==> post(func(s[k]), visited[k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.func == o.func
            && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
                s.len() == visited.len()
                    && I::produces(self.iter, s, o.iter)
                    && forall(|k: thrust_models::model::Int|
                        !(0 <= k && k < visited.len())
                            || thrust_macros::post!((self.func)(s[k]), visited[k])))
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
