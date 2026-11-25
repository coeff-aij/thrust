//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Fail twin: the client asserts `v > 0` of the first item, 0, which the predicate accepts.
// Creusot's `examples/iterators/17_filter.rs` (3620de437): `Filter` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations, in Creusot's own form: `produces` relates the visited
// items to the inner iterator's sequence `s` through a monotone index map `f` (Creusot's
// `Mapping<Int, Int>`, here an `Array<Int, Int>`), and an item of `s` is visited exactly when the
// predicate's postcondition holds for `true`. `no_precondition`, `immutable` and `precise` are
// predicates of the closure type, over every closure state, and `invariant` states them with the
// inner iterator's. `next`'s loop invariant restates what Creusot carries implicitly (the
// prophecy of the reborrow, as in `skip.rs`, and the type invariant), and keeps Creusot's `produced`
// as the existential `t`. `produces_trans` calls the lemma `produces_trans_at`, which names the joined
// witness: the inner sequences concatenated and the index maps joined by `Array::from_fn`, Creusot's
// `Mapping` built by a closure. The `resolve` of Creusot's `completed` has no counterpart: Thrust
// has no `resolve` predicate (fork issue #156). The client calls `next` at `Range` where Creusot's
// `less_than` collects a `Vec` from std's `filter`.
use thrust_models::FnParam; use thrust_models::model::{Array, Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Filter<I, F> {
    iter: I,
    func: F,
}

// The model is the tuple (iter, func), read as `.0` and `.1` in the specifications.
impl<I: Model, F> Model for Filter<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I, F> Filter<I, F>
where
    I: Iterator + Model,
    F: FnMut(&I::Item) -> bool,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    // Creusot's `no_precondition`: the predicate may be called on every item in every state.
    #[thrust_macros::predicate]
    fn no_precondition() -> bool {
        forall(|c: Closure<F>, i: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(i)))
    }

    // Creusot's `immutable`: the predicate's state does not change.
    #[thrust_macros::predicate]
    fn immutable() -> bool {
        forall(|c: Closure<F>, d: Closure<F>| !thrust_macros::hist_inv!(c, d) || c == d)
    }

    // Creusot's `precise`: no call has both results.
    #[thrust_macros::predicate]
    fn precise() -> bool {
        forall(|c: Closure<F>, d: Closure<F>, i: <<I as Iterator>::Item as Model>::Ty|
            !(thrust_macros::post!(Mut::new(c, d)(i), true) && thrust_macros::post!(Mut::new(c, d)(i), false)))
    }

    // Creusot's `Invariant` of `Filter`, the guard of `produces`.
    #[thrust_macros::predicate]
    fn func_invariant() -> bool {
        Self::no_precondition() && Self::immutable() && Self::precise()
    }

    // `produces` with the inner sequence `s` and the index map `f` given: the body of Creusot's
    // `exists<s, f>`.
    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Seq<<<I as Iterator>::Item as Model>::Ty>, o: Self, s: Seq<<<I as Iterator>::Item as Model>::Ty>, f: Array<Int, Int>) -> bool {
        I::produces(s0.0, s, o.0)
            && forall(|i: Int, j: Int| !(0 <= i && i <= j && j < visited.len())
                || (0 <= f[i] && f[i] <= f[j] && f[j] < s.len()))
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == s[f[i]])
            && forall(|i: Int| !(0 <= i && i < s.len())
                || ((!exists(|j: Int| 0 <= j && j < visited.len() && f[j] == i)
                        || thrust_macros::post!(Mut::new(s0.1, s0.1)(s[i]), true))
                    && (!thrust_macros::post!(Mut::new(s0.1, s0.1)(s[i]), true)
                        || exists(|j: Int| 0 <= j && j < visited.len() && f[j] == i))))
    }

    // `produces_at` of the joined witnesses: the inner sequences concatenated and the index maps
    // joined, the second shifted past the first's inner sequence (Creusot's `Mapping` built by a
    // closure, here `Array::from_fn`).
    #[thrust_macros::ensures(forall(|s1: Seq<<<I as Iterator>::Item as Model>::Ty>| forall(|s2: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|f1: Array<Int, Int>| forall(|f2: Array<Int, Int>|
        !(Self::func_invariant()
            && thrust_macros::hist_inv!(a.1, b.1)
            && Self::produces_at(a, ab, b, s1, f1)
            && Self::produces_at(b, bc, c, s2, f2))
            || Self::produces_at(a, ab.concat(bc), c, s1.concat(s2),
                Array::<Int, Int>::from_fn(|i: Int| if i < ab.len() { f1[i] } else { f2[i - ab.len()] + s1.len() })))))))]
    #[thrust_macros::lemma]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // `produces`'s existentials introduced at the joined witnesses.
    #[thrust_macros::ensures(forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| forall(|f: Array<Int, Int>|
        !(Self::func_invariant()
            && thrust_macros::hist_inv!(a.1, c.1)
            && Self::produces_at(a, ab.concat(bc), c, s, f))
            || <Self as Iterator>::produces(a, ab.concat(bc), c))))]
    #[thrust_macros::lemma]
    fn produces_join_intro(
        a: Ghost<Self>,
        ab: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        bc: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // `produces_trans` on ghost arguments: `produces_at` of the joined witnesses, then the
    // introduction of `produces`'s existentials at them.
    #[thrust_macros::requires(<Self as Iterator>::produces(a, ab, b)
        && <Self as Iterator>::produces(b, bc, c))]
    #[thrust_macros::ensures(<Self as Iterator>::produces(a, ab.concat(bc), c))]
    #[thrust_macros::lemma]
    fn produces_trans_split(
        a: Ghost<Self>,
        ab: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>,
        c: Ghost<Self>,
    ) {
        Self::produces_trans_at(a, ab, b, bc, c);
        Self::produces_join_intro(a, ab, bc, c);
    }
}

#[thrust_macros::context]
impl<I, F> Iterator for Filter<I, F>
where
    I: Iterator + Model,
    F: FnMut(&I::Item) -> bool,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    type Item = I::Item;

    // Creusot's `next`: the inner items consumed so far are all refused by the predicate, and the
    // inner iterator produced them from its state at entry. Creusot keeps them in a snapshot
    // `produced`; here they are the existential `t` of the invariant, which also restates the
    // type invariant that Creusot carries implicitly.
    fn next(&mut self) -> Option<I::Item> {
        let s = self;
        I::produces_refl(&s.iter);
        loop {
            thrust_macros::invariant!(
                |s: &mut Self, self: FnParam<&mut Self>|
                !s == !self.at_entry()
                    && Self::invariant(*s)
                    && (*s).1 == (*self.at_entry()).1
                    && exists(|t: Seq<<<I as Iterator>::Item as Model>::Ty>|
                        forall(|i: Int| !(0 <= i && i < t.len())
                            || thrust_macros::post!(Mut::new((*s).1, (*s).1)(t[i]), false))
                        && I::produces((*self.at_entry()).0, t, (*s).0))
            );
            match s.iter.next() {
                None => return None,
                Some(n) => {
                    if (s.func)(&n) {
                        return Some(n);
                    }
                }
            }
        }
    }



    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::no_precondition() && Self::immutable() && Self::precise() && I::invariant(self.0)
    }

    // Creusot's `completed`: the inner iterator, after some items all refused, is completed, and
    // the predicate's state is unchanged.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| exists(|e: <I as Model>::Ty| exists(|e2: <I as Model>::Ty|
            I::produces((*self).0, s, e)
                && I::completed(Mut::new(e, e2))
                && forall(|i: Int| !(0 <= i && i < s.len())
                    || thrust_macros::post!(Mut::new((*self).1, (!self).1)(s[i]), false)))))
            && (*self).1 == (!self).1
    }

    // Creusot's `produces`, under Creusot's `Invariant` of `Filter` (the three conditions on the
    // predicate, not the inner iterator's invariant).
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, succ: Self) -> bool {
        !Self::func_invariant()
            || (thrust_macros::hist_inv!(self.1, succ.1)
                && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| exists(|f: Array<Int, Int>| Self::produces_at(self, visited, succ, s, f))))
    }

    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<<I as Iterator>::Item as Model>::Ty>| -> Seq<<<I as Iterator>::Item as Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<<I as Iterator>::Item as Model>::Ty>| -> Seq<<<I as Iterator>::Item as Model>::Ty> { bc });
        Self::produces_trans_split(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }
}

// Creusot's `filter`.
#[thrust_macros::context]
#[thrust_macros::requires(Filter::<I, P>::immutable())]
#[thrust_macros::requires(Filter::<I, P>::no_precondition())]
#[thrust_macros::requires(Filter::<I, P>::precise())]
#[thrust_macros::ensures(result.0 == iter && result.1 == f)]
fn filter<I, P>(iter: I, f: P) -> Filter<I, P>
where
    I: Iterator + Model,
    P: FnMut(&I::Item) -> bool,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    Filter { iter, func: f }
}

#[derive(PartialEq)]
struct Range {
    start: isize,
    end: isize,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = isize;

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

#[thrust_macros::requires(true)]
pub fn client() {
    let p = thrust_macros::closure!(
        requires(true),
        ensures(result == (*i < 5)),
        |i: &isize| -> bool { *i < 5 },
    );
    let mut it = filter(Range { start: 0, end: 10 }, p);
    let r = it.next();
    thrust_macros::proof_assert!(|r: Option<isize>| forall(|v: Int| r == Some(v) ==> v > 0));
}
