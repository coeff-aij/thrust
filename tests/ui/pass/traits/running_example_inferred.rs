//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3

// The inferred-invariant half of the paper's running example (see `running_example.rs` for the
// written-invariant, composed-with-`Map` half). `count` is generic over any `Iterator`, and its
// loop invariant is inferred rather than written; verified here in isolation, over the abstract
// `I`, with no call site (`Map` and `Range` are unused). Composing this inference with the
// `Map`-wrapped call site of `running_example.rs` currently times out on this build.
use thrust_models::model::{Closure, Mut};
use thrust_models::{forall, Model};

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    // `step` relates one call of `next` to its successor state, so an invariant guarded by it
    // is not preserved by `next`. `produces` is monotone under `next`, which is what makes the
    // guard inductive.
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces(!self, i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// `item` is among what `self` may still produce.
    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool;
}

#[derive(PartialEq)]
struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = Map<<I as Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I: Iterator + Model, B: Model, F: Fn(I::Item) -> B> Iterator for Map<I, F>
where
    <I as Model>::Ty: PartialEq + Model<Ty = <I as Model>::Ty>,
    <I::Item as Model>::Ty: PartialEq,
    <B as Model>::Ty: PartialEq,
    I::Item: Model,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
            && forall(|i: <I::Item as Model>::Ty| !I::produces(self.iter, i) || thrust_macros::pre!((self.func)(i)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    // `item` has the model type of `Self::Item = B`, which the generic instantiation of this
    // impl does not resolve to a concrete sort when the body is Rust syntax (the outer `item`
    // parameter keeps an unresolved forall-sort at the call site, and CoAR then rejects the
    // query as ill-sorted). Falling back to a hand-written SMT-LIB2 body for exactly the two
    // predicates whose signature mentions `Self::Item` avoids the gap; `invariant` and
    // `completed` do not name `Self::Item` in their own signature and stay Rust syntax.
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: I::Item| I::step(self.iter, i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(and
            (exists ((i a6))
                (and
                    (q_step_80a678896b59f2fe43807b7a6c151bd<a0>
                        (tuple_proj<a0-a1>.0 self_)
                        i
                        (tuple_proj<a0-a1>.0 dist)
                    )
                    (q_pre_next_80a678896b59f2f8a00f12b3b2834c2<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                    )
                    (q_post_next_80a678896b59f2f8a00f12b3b2834c2<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                        item
                    )
                )
            )
            (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: I::Item| I::produces(self.iter, j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        "(exists ((j a6))
            (and
                (q_produces_80a678896b59f2fe3bec549d2dd6563<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    j
                )
                (q_pre_next_80a678896b59f2f8a00f12b3b2834c2<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                )
                (q_post_next_80a678896b59f2f8a00f12b3b2834c2<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                    item
                )
            )
        )";
        true
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

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        !((*self).start < (*self).end) && (*self) == (!self)
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        self.start < self.end
            && item == self.start
            && dist.start == self.start + 1
            && dist.end == self.end
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        self.start <= item && item < self.end
    }
}

// A generic consumer over any `Iterator`, with an inferred (not written) loop invariant.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(*it))]
#[thrust_macros::ensures(I::invariant(!it) && result >= 0)]
fn count<I: Iterator + thrust_models::Model>(it: &mut I) -> i64
where
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    let mut n = 0;
    while let Some(_) = it.next() {
        n += 1;
    }
    n
}

fn main() {}
