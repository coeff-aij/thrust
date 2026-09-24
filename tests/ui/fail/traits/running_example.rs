//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3

// The paper's running example: a generic `Map` adapter (Rust-syntax predicate bodies, #114)
// over a `Range` source, consumed by a generic `count` whose loop invariant is inferred, not
// written. The call site's closure is defined on every value a `1..5` range can still produce,
// which is exactly what `Map::invariant` requires at that instantiation.
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
                    (q_step_eea9e2afb6eaca40b1a4a543d69a876<a0>
                        (tuple_proj<a0-a1>.0 self_)
                        i
                        (tuple_proj<a0-a1>.0 dist)
                    )
                    (q_pre_next_eea9e2afb6eaca4011a8320e527efe68<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                    )
                    (q_post_next_eea9e2afb6eaca4011a8320e527efe68<a1>
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
                (q_produces_eea9e2afb6eaca4081fc747a03d38f0b<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    j
                )
                (q_pre_next_eea9e2afb6eaca4011a8320e527efe68<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                )
                (q_post_next_eea9e2afb6eaca4011a8320e527efe68<a1>
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

// The call site: the mapper is defined on every positive value, and every item a `1..5` range
// can still produce is positive, so `Map`'s invariant holds at this instantiation.
fn main() {
    let f = thrust_macros::closure!(
        requires(x > 1),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let mut m = Map {
        iter: Range { start: 1, end: 5 },
        func: f,
    };
    let n = count(&mut m);
    assert!(n >= 0);
}
