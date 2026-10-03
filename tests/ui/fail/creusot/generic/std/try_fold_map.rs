//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1 THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// std's `Iterator::try_fold` (its body as std writes it, `?` on each call), generic in the iterator,
// the accumulator `B` and an `FnMut` closure, with the `Try` type fixed to `Option<B>`, specified in
// the form of Creusot's `Map` (`map.rs`): the closure states and accumulators along the produced
// items form a chain in which each step is a call returning `Some`, and the closure may be called
// at every state the chain reaches. `Some(r)` ends a chain over a completed iterator with `r`; `None`
// is a call returning `None` at the end of a chain. The specification says nothing of the client's
// property; `main` derives it from the chain.
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


// The chain from `iter`, `init` and `f` along `s` to the iterator state `it`.
#[thrust_macros::context]
#[thrust_macros::predicate]
fn try_fold_chain<I, B, F>(iter: I, init: B, f: F, s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: I, accs: Seq<<B as Model>::Ty>, fs: Seq<F>) -> bool
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> Option<B>,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    I::produces(iter, s, it)
        && accs.len() == s.len() + 1
        && fs.len() == s.len() + 1
        && accs[0] == init
        && fs[0] == f
        && thrust_macros::hist_inv!(f, fs[s.len()])
        && forall(|k: Int| !(0 <= k && k < s.len())
            || (thrust_macros::hist_inv!(f, fs[k])
                && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(accs[k], s[k]), Some(accs[k + 1]))))
}

// The chain extended by one item: the next item `x`, the call's result `r` and the closure's state
// after it, `g`, pushed onto the three sequences.
#[thrust_macros::context]
#[thrust_macros::ensures(forall(|iter: <I as Model>::Ty, init: <B as Model>::Ty, f: Closure<F>, s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty, r: <B as Model>::Ty, g: Closure<F>|
    !(try_fold_chain::<I, B, F>(iter, init, f, s, it, accs, fs)
        && I::produces(it, Seq::singleton(x), it2)
        && thrust_macros::post!(Mut::new(fs[s.len()], g)(accs[s.len()], x), Some(r)))
        || try_fold_chain::<I, B, F>(iter, init, f, s.push(x), it2, accs.push(r), fs.push(g))))]
fn try_fold_chain_push<I, B, F>()
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> Option<B>,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
}

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(*iter))]
#[thrust_macros::requires(forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty|
    !(try_fold_chain::<I, B, F>(*iter, init, f, s, it, accs, fs) && I::produces(it, Seq::singleton(x), it2))
        || thrust_macros::pre!(fs[s.len()](accs[s.len()], x))))]
#[thrust_macros::ensures(forall(|r: <B as Model>::Ty| !(result == Some(r)) || exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>|
    try_fold_chain::<I, B, F>(*iter, init, f, s, it, accs, fs)
        && accs[s.len()] == r
        && I::completed(Mut::new(it, !iter)))))]
#[thrust_macros::ensures(!(result == None) || exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, g: Closure<F>|
    try_fold_chain::<I, B, F>(*iter, init, f, s, it, accs, fs)
        && I::produces(it, Seq::singleton(x), !iter)
        && thrust_macros::post!(Mut::new(fs[s.len()], g)(accs[s.len()], x), None::<<B as Model>::Ty>)))]
fn try_fold<I, B, F>(iter: &mut I, init: B, f: F) -> Option<B>
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> Option<B>,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    let it = iter;
    let mut accum = init;
    let mut g = f;
    I::produces_refl(it);
    // The chain so far: the produced items, the accumulators and the closure states.
    let mut gs = thrust_macros::ghost!(|| -> Seq<<<I as Iterator>::Item as Model>::Ty> { Seq::empty() });
    let mut gaccs = thrust_macros::ghost!(|accum: B| -> Seq<<B as Model>::Ty> { Seq::singleton(accum) });
    let mut gfs = thrust_macros::ghost!(|g: F| -> Seq<Closure<F>> { Seq::singleton(g) });
    loop {
        thrust_macros::invariant!(
            |it: &mut I, accum: B, g: F, gs: thrust_models::Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, gaccs: thrust_models::Ghost<Seq<<B as Model>::Ty>>, gfs: thrust_models::Ghost<Seq<Closure<F>>>, iter: thrust_models::FnParam<&mut I>, init: thrust_models::FnParam<B>, f: thrust_models::FnParam<F>|
            !it == !iter.at_entry()
                && I::invariant(*it)
                && forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it1: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty|
                    !(try_fold_chain::<I, B, F>(*iter.at_entry(), init.at_entry(), f.at_entry(), s, it1, accs, fs) && I::produces(it1, Seq::singleton(x), it2))
                        || thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
                && try_fold_chain::<I, B, F>(*iter.at_entry(), init.at_entry(), f.at_entry(), gs, *it, gaccs, gfs)
                && gaccs[gs.len()] == accum
                && gfs[gs.len()] == g
        );
        match it.next() {
            None => {
                // Keeps the chain live at the loop header.
                let _live = (&gs, &gaccs, &gfs);
                return Some(accum);
            }
            Some(x) => {
                let gx = thrust_macros::ghost!(|x: <I as Iterator>::Item| -> <I as Iterator>::Item { x });
                accum = g(accum, x)?;
                try_fold_chain_push::<I, B, F>();
                let ngs = thrust_macros::ghost!(|gs: thrust_models::Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, gx: thrust_models::Ghost<<I as Iterator>::Item>| -> Seq<<<I as Iterator>::Item as Model>::Ty> { gs.push(gx) });
                let ngaccs = thrust_macros::ghost!(|gaccs: thrust_models::Ghost<Seq<<B as Model>::Ty>>, accum: B| -> Seq<<B as Model>::Ty> { gaccs.push(accum) });
                let ngfs = thrust_macros::ghost!(|gfs: thrust_models::Ghost<Seq<Closure<F>>>, g: F| -> Seq<Closure<F>> { gfs.push(g) });
                // Keeps the previous chain live at the snapshots above.
                let _live = (&gs, &gaccs, &gfs, &gx);
                gs = ngs;
                gaccs = ngaccs;
                gfs = ngfs;
            }
        }
    }
}

fn main() {
    let c = thrust_macros::closure!(
        requires(a >= 0),
        ensures(forall(|r: Int| !(result == Some(r)) || r >= 0)),
        |a: isize, x: isize| -> Option<isize> { if x > a { Some(x) } else { Some(a) } },
    );
    let mut it = Range { start: 0, end: 10 };
    let r = try_fold(&mut it, 0, c);
    assert!(match r { Some(v) => v >= 1, None => true });
}
