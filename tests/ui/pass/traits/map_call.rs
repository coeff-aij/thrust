//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

// The generic `Map` adapter used at a call site.
//
// `Map` is written once, over an inner iterator `I` and a mapper `F`, and its
// predicates speak of the item type as an abstract sort. `main` builds a `Map`
// over a concrete range and a closure that is only defined on positive
// arguments, so entering `next` there needs the adapter's invariant — the
// mapper is defined on everything the inner iterator can still produce — read
// at that instantiation.
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    // `step` relates one call of `next` to its successor state, so an invariant
    // guarded by it ("closure pre for what the inner can step to NOW") is not
    // preserved by `next`. `produces` is monotone under `next`, which is what makes
    // the guard inductive.
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

struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<I, F>;
}

#[thrust_macros::context]
impl<I: Iterator + thrust_models::Model, B: thrust_models::Model, F: Fn(I::Item) -> B> Iterator for Map<I, F>
where <I as thrust_models::Model>::Ty: PartialEq
{
    type Item = B;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some((self.func)(v))
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|i: I::Item| self.iter.produces(i) ==> pre!(self.func(i)))
        "(and
            (q_invariant_c77f3ed2bdc90876d8a92ae0055fafce<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((i a3))
                (=>
                    (q_produces_c77f3ed2bdc9087674032fbac803b928<a0>
                        (tuple_proj<a0-a1>.0 self_)
                        i
                    )
                    (q_pre_F_c77f3ed2bdc908764a99b2a43be14ee1<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                    )
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_c77f3ed2bdc9087656f1918e29927d7b<a0>
                (mut<a0>
                    (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_))
                    (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_))
                (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: I::Item| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(exists ((i a3))
            (and
                (q_step_c77f3ed2bdc908765448fab8de8fd8dc<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    i
                    (tuple_proj<a0-a1>.0 dist)
                )
                (q_pre_F_c77f3ed2bdc908764a99b2a43be14ee1<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
                (q_post_F_c77f3ed2bdc908764a99b2a43be14ee1<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                    item
                )
                (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: I::Item| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        "(exists ((j a3))
            (and
                (q_produces_c77f3ed2bdc9087674032fbac803b928<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    j
                )
                (q_pre_F_c77f3ed2bdc908764a99b2a43be14ee1<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                )
                (q_post_F_c77f3ed2bdc908764a99b2a43be14ee1<a1>
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

impl thrust_models::Model for Range {
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
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // !(*self.start < *self.end) && *self == !self
        "(and
            (not (<
                (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_))
            ))
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.start < self.end && self.end == dist.end && self.start == item
        // && self.start + 1 == dist.start
        "(and
            (< (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.1 self_))
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // self.start <= item && item < self.end
        "(and
            (<= (tuple_proj<Int-Int>.0 self_) item)
            (< item (tuple_proj<Int-Int>.1 self_))
        )";
        true
    }
}

// The call site the guard is for: the mapper is only defined for positive
// arguments, and every item a `1..5` range can produce is positive.
fn main() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let mut m = Map {
        iter: Range { start: 1, end: 5 },
        func: f,
    };
    let _ = m.next();
}
