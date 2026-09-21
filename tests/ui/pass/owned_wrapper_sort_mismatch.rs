//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

// Laws as body-less trait methods (Creusot's `#[law]` in the trait), proven by each impl and
// CALLED at the loop instead of delivering transitivity as an ensures on `next`.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
    <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>| result == Some(i) && s.len() == 1 && s[0] == i ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

    #[thrust_macros::requires(
        Self::produces(a, ab, b)
            && Self::step(b, i, c)
    )]
    #[thrust_macros::ensures(forall(|t: Seq<<Self::Item as Model>::Ty>| t == ab.push(i) ==> Self::produces(a, t, c)))]
    fn produces_step(
        a: Ghost<<Self as Model>::Ty>,
        ab: Ghost<Seq<<Self::Item as Model>::Ty>>,
        b: Ghost<<Self as Model>::Ty>,
        i: Ghost<<Self::Item as Model>::Ty>,
        c: Ghost<<Self as Model>::Ty>,
    );

    // What a generic caller needs when `next` reports exhaustion. `completed` is abstract
    // there, so nothing on its own connects the iterator handed back to the state the loop
    // invariant had reached; an iterator that legitimately writes to itself on the exhausted
    // path (setting a flag, emptying a slot) still preserves every history that led to it.
    #[thrust_macros::requires(Self::completed(thrust_models::model::Mut::new(cur, fin)))]
    #[thrust_macros::ensures(forall(|b: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| Self::produces(b, s, cur) ==> Self::produces(b, s, fin))))]
    fn exhaustion_preserves_produces(
        cur: Ghost<<Self as Model>::Ty>,
        fin: Ghost<<Self as Model>::Ty>,
    );

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
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

    fn produces_step(a: Ghost<Range>, ab: Ghost<Seq<Int>>, b: Ghost<Range>, i: Ghost<Int>, c: Ghost<Range>) {}

    fn exhaustion_preserves_produces(cur: Ghost<Range>, fin: Ghost<Range>) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
            (>= (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_)))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(and
            (< (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.1 self_))
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<Int>, o: Self) -> bool {
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

struct Run<I: Iterator<Item = i64> + Model>
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    iter: I,
    produced: Ghost<Seq<Int>>,
}

impl<I: Iterator<Item = i64> + Model> Model for Run<I>
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    type Ty = (<I as Model>::Ty, Seq<Int>);
}

// The loop calls the laws (Creusot's `produces_refl` at entry, `produces_trans` per step) on
// ghost snapshots taken around `next`, instead of relying on a one-step ensures of `next`.
// Item is fixed to i64 because the singleton `[x]` handed to the law is built with
// `Seq::singleton`, which at a generic Item needs the abstract sort's default element.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant((*r).0) && init == (*r).0 && (*r).1.len() == 0)]
#[thrust_macros::ensures(I::produces(init, (!r).1, (!r).0))]
fn drain<I: Iterator<Item = i64> + Model>(r: &mut Run<I>, init: Ghost<<I as Model>::Ty>)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
{
    I::produces_refl(&r.iter);
    let rr = r;
    loop {
        thrust_macros::invariant!(
            |rr: &mut Run<I>, r: thrust_models::FnParam<&mut Run<I>>, init: thrust_models::FnParam<Ghost<<I as Model>::Ty>>|
            I::invariant((*rr).0)
                && !rr == !r.at_entry()
                && I::produces(init.at_entry(), (*rr).1, (*rr).0)
        );
        let pre = thrust_macros::ghost!(|rr: &mut Run<I>| -> <I as Model>::Ty { (*rr).0 });
        let before = thrust_macros::ghost!(|rr: &mut Run<I>| -> Seq<Int> { (*rr).1 });
        // The snapshot is taken before the match so that `rr` is still live on the exit arm.
        let outcome = rr.iter.next();
        let post = thrust_macros::ghost!(|rr: &mut Run<I>| -> <I as Model>::Ty { (*rr).0 });
        match outcome {
            Some(x) => {
                let item = thrust_macros::ghost!(|x: i64| -> Int { x });
                I::produces_step(init, before, pre, item, post);
                rr.produced = thrust_macros::ghost!(|rr: &mut Run<I>, x: i64| -> Seq<Int> { (*rr).1.push(x) });
                let _keep: i64 = x + 0;
            }
            None => {
                I::exhaustion_preserves_produces(pre, post);
                break;
            }
        }
    }
}

// Owned entry point: build the `Run` here, run the `&mut` loop, hand the `Run` back.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter) && init == iter)]
#[thrust_macros::ensures(I::produces(init, result.1, result.0))]
fn drain_owned<I: Iterator<Item = i64> + Model>(iter: I, init: Ghost<<I as Model>::Ty>) -> Run<I>
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
{
    let mut run = Run {
        iter,
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    drain(&mut run, init);
    run
}

fn main() {}
