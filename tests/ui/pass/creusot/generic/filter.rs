//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

/// The model of `usize`, which carries its width while `THRUST_INT_RANGE` is set: `Seq::len`
/// returns it, and the ghost `idx` holds lengths.
#[cfg(not(thrust_int_range))]
type USize = thrust_models::model::UInt;
#[cfg(thrust_int_range)]
type USize = thrust_models::model::UIntN<64>;

// `filter` collected into a `Vec`, generic in the iterator `I` and an `FnMut` predicate `P`, as
// std's `iter.filter(p).collect::<Vec<_>>()` is (with the predicate taking the item by value,
// `I::Item: Copy`, where std passes `&I::Item`).
// No Creusot counterpart; `main` calls it at `Range` with a concrete closure.

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

// The calls of the predicate along `s`: `fs[k]` is its state before the call on `s[k]`, which
// returned `bs[k]`, and `fs[0]` is `p`.
#[thrust_macros::predicate]
fn filter_chain<I, P>(p: P, s: Seq<<<I as Iterator>::Item as Model>::Ty>, bs: Seq<bool>, fs: Seq<Closure<P>>) -> bool
where
    I: Iterator + Model,
    P: FnMut(I::Item) -> bool,
{
    bs.len() == s.len()
        && fs.len() == s.len() + 1
        && fs[0] == p
        && forall(|k: Int| !(0 <= k && k < s.len())
            || thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), bs[k]))
}

// `out` is the subsequence of `s` at the positions where `bs` is `true`, in order: Creusot's
// `Filter::produces`, with the index map `idx`.
#[thrust_macros::predicate]
fn filter_kept<I>(s: Seq<<<I as Iterator>::Item as Model>::Ty>, bs: Seq<bool>, idx: Seq<USize>, out: Seq<<<I as Iterator>::Item as Model>::Ty>) -> bool
where
    I: Iterator + Model,
{
    out.len() == idx.len()
        && forall(|j: Int| !(0 <= j && j < idx.len())
            || (0 <= idx[j] && idx[j] < s.len() && out[j] == s[idx[j]] && bs[idx[j]]))
        && forall(|i: Int, j: Int| !(0 <= i && i < j && j < idx.len()) || idx[i] < idx[j])
        && forall(|k: Int| !(0 <= k && k < s.len() && bs[k])
            || exists(|j: Int| 0 <= j && j < idx.len() && idx[j] == k))
}

// `filter` collected into a `Vec` over any iterator, in the `produces` form: `iter` produced `s`
// and then completed, the predicate's calls along `s` returned `bs`, and the result is the items
// of `s` it accepted, in order. The predicate may be called on every item in every state.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::requires(forall(|c: Closure<P>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x))))]
#[thrust_macros::ensures(exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, done: <I as Model>::Ty, fin: <I as Model>::Ty, bs: Seq<bool>, fs: Seq<Closure<P>>, idx: Seq<USize>|
    I::produces(iter, s, done)
        && I::completed(Mut::new(done, fin))
        && filter_chain::<I, P>(p, s, bs, fs)
        && filter_kept::<I>(s, bs, idx, result)))]
fn filter<I, P>(iter: I, p: P) -> Vec<I::Item>
where
    I: Iterator + Model,
    P: FnMut(I::Item) -> bool,
    <I as Iterator>::Item: Model + Copy,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
{
    let mut it = iter;
    let mut q = p;
    let mut out: Vec<I::Item> = Vec::new();
    I::produces_refl(&it);
    // The produced items, the predicate's answers and states, and the positions kept.
    let mut gs = thrust_macros::ghost!(|| -> Seq<<<I as Iterator>::Item as Model>::Ty> { Seq::empty() });
    let mut gbs = thrust_macros::ghost!(|| -> Seq<bool> { Seq::empty() });
    let mut gfs = thrust_macros::ghost!(|q: P| -> Seq<Closure<P>> { Seq::singleton(q) });
    let mut gidx = thrust_macros::ghost!(|| -> Seq<USize> { Seq::empty() });
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: I, q: P, out: Vec<I::Item>, gs: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, gbs: Ghost<Seq<bool>>, gfs: Ghost<Seq<Closure<P>>>, gidx: Ghost<Seq<USize>>, iter: thrust_models::FnParam<I>, p: thrust_models::FnParam<P>|
            I::invariant(it)
                && I::produces(iter.at_entry(), gs, it)
                && forall(|c: Closure<P>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x)))
                && filter_chain::<I, P>(p.at_entry(), gs, gbs, gfs)
                && gfs[gs.len()] == q
                && filter_kept::<I>(gs, gbs, gidx, out)
        );
        let b = q(x);
        if b {
            out.push(x);
            gidx = thrust_macros::ghost!(|gidx: Ghost<Seq<USize>>, gs: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>| -> Seq<USize> { gidx.push(gs.len()) });
        }
        gs = thrust_macros::ghost!(|gs: Ghost<Seq<<<I as Iterator>::Item as Model>::Ty>>, x: I::Item| -> Seq<<<I as Iterator>::Item as Model>::Ty> { gs.push(x) });
        gbs = thrust_macros::ghost!(|gbs: Ghost<Seq<bool>>, b: bool| -> Seq<bool> { gbs.push(b) });
        gfs = thrust_macros::ghost!(|gfs: Ghost<Seq<Closure<P>>>, q: P| -> Seq<Closure<P>> { gfs.push(q) });
    }
    out
}

fn main() {
    let c = thrust_macros::closure!(
        ensures(result == (x >= 5)),
        |x: isize| -> bool { x >= 5 },
    );
    let v = filter(Range { start: 0, end: 10 }, c);
    if v.len() > 0 {
        assert!(v[0] >= 5);
    }
}
