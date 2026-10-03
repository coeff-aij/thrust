//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::model::{Array, Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `Filter` (`examples/iterators/17_filter.rs` of creusot-rs/creusot 3620de437) in its
// own form: `produces` relates the visited items to the inner iterator's sequence `s` through a
// monotone index map `f` (Creusot's `Mapping<Int, Int>`, here an `Array<Int, Int>`), and an item
// of `s` is visited exactly when the predicate's postcondition holds for `true`. The invariant is
// Creusot's `no_precondition`, `immutable` and `precise` of the predicate, over every closure state.
// `next` is Creusot's loop with its three invariants. The client calls `next` at `Range` where
// Creusot's collects a `Vec`.
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

struct Filter<I, F> {
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
        while let Some(n) = s.iter.next() {
            thrust_macros::invariant!(
                |s: &mut Self, self: thrust_models::FnParam<&mut Self>|
                Self::invariant(*s)
                    && (*s).1 == (*self.at_entry()).1
                    && exists(|t: Seq<<<I as Iterator>::Item as Model>::Ty>|
                        forall(|i: Int| !(0 <= i && i < t.len())
                            || thrust_macros::post!(Mut::new((*s).1, (*s).1)(t[i]), false))
                        && I::produces((*self.at_entry()).0, t, (*s).0))
            );
            if (s.func)(&n) {
                return Some(n);
            }
        }
        None
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
        !(Self::no_precondition() && Self::immutable() && Self::precise())
            || (thrust_macros::hist_inv!(self.1, succ.1)
                && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>| exists(|f: Array<Int, Int>|
                    I::produces(self.0, s, succ.0)
                        && forall(|i: Int, j: Int| !(0 <= i && i <= j && j < visited.len())
                            || (0 <= f[i] && f[i] <= f[j] && f[j] < s.len()))
                        && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == s[f[i]])
                        && forall(|i: Int| !(0 <= i && i < s.len())
                            || ((!exists(|j: Int| 0 <= j && j < visited.len() && f[j] == i)
                                    || thrust_macros::post!(Mut::new(self.1, self.1)(s[i]), true))
                                && (!thrust_macros::post!(Mut::new(self.1, self.1)(s[i]), true)
                                    || exists(|j: Int| 0 <= j && j < visited.len() && f[j] == i)))))))
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

fn main() {
    let p = thrust_macros::closure!(
        requires(true),
        ensures(result == (*i < 5)),
        |i: &isize| -> bool { *i < 5 },
    );
    let mut it = filter(Range { start: 0, end: 10 }, p);
    let r = it.next();
    assert!(match r { Some(v) => v < 5, None => true });
}
