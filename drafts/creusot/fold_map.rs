//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// std's `Iterator::fold` (its body as std writes it), generic in the iterator, the accumulator `B`
// and an `FnMut` closure, with a specification in the form of Creusot's `Map` (`map.rs`): the
// closure states `fs` and the accumulators `accs` along the produced items `s` form a chain in
// which each step is a call's postcondition, and the closure may be called at every state the
// chain reaches. The result is the chain's last accumulator once the iterator is completed. The
// specification says nothing of the client's property; `main` derives it from the chain.
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
fn fold_chain<I, B, F>(iter: I, init: B, f: F, s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: I, accs: Seq<<B as Model>::Ty>, fs: Seq<F>) -> bool
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> B,
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
                && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(accs[k], s[k]), accs[k + 1])))
}

// The chain extended by one item: the next item `x`, the call's result `r` and the closure's state
// after it, `g`, pushed onto the three sequences.
#[thrust_macros::context]
#[thrust_macros::ensures(forall(|iter: <I as Model>::Ty, init: <B as Model>::Ty, f: Closure<F>, s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty, r: <B as Model>::Ty, g: Closure<F>|
    !(fold_chain::<I, B, F>(iter, init, f, s, it, accs, fs)
        && I::produces(it, Seq::singleton(x), it2)
        && thrust_macros::post!(Mut::new(fs[s.len()], g)(accs[s.len()], x), r))
        || fold_chain::<I, B, F>(iter, init, f, s.push(x), it2, accs.push(r), fs.push(g))))]
fn fold_chain_push<I, B, F>()
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
}

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::requires(forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty|
    !(fold_chain::<I, B, F>(iter, init, f, s, it, accs, fs) && I::produces(it, Seq::singleton(x), it2))
        || thrust_macros::pre!(fs[s.len()](accs[s.len()], x))))]
#[thrust_macros::ensures(exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, it2: <I as Model>::Ty|
    fold_chain::<I, B, F>(iter, init, f, s, it, accs, fs)
        && accs[s.len()] == result
        && I::completed(Mut::new(it, it2))))]
fn fold<I, B, F>(iter: I, init: B, f: F) -> B
where
    I: Iterator + Model,
    B: Model,
    F: FnMut(B, I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    let mut it = iter;
    let mut accum = init;
    let mut g = f;
    I::produces_refl(&it);
    loop {
        thrust_macros::invariant!(
            |it: I, accum: B, g: F, iter: thrust_models::FnParam<I>, init: thrust_models::FnParam<B>, f: thrust_models::FnParam<F>|
            I::invariant(it)
                && forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, it1: <I as Model>::Ty, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>, x: <<I as Iterator>::Item as Model>::Ty, it2: <I as Model>::Ty|
                    !(fold_chain::<I, B, F>(iter.at_entry(), init.at_entry(), f.at_entry(), s, it1, accs, fs) && I::produces(it1, Seq::singleton(x), it2))
                        || thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
                && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>, accs: Seq<<B as Model>::Ty>, fs: Seq<Closure<F>>|
                    fold_chain::<I, B, F>(iter.at_entry(), init.at_entry(), f.at_entry(), s, it, accs, fs)
                        && accs[s.len()] == accum
                        && fs[s.len()] == g)
        );
        match it.next() {
            None => return accum,
            Some(x) => {
                accum = g(accum, x);
                fold_chain_push::<I, B, F>();
            }
        }
    }
}

fn main() {
    let c = thrust_macros::closure!(
        requires(a >= 0),
        ensures(result >= 0),
        |a: isize, x: isize| -> isize { if x > a { x } else { a } },
    );
    let r = fold(Range { start: 0, end: 10 }, 0, c);
    assert!(r >= 0);
}
