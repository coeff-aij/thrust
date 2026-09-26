//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
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

struct Run<I: Iterator<Item = i64> + Model> {
    iter: I,
    items: Ghost<Seq<Int>>,
    accs: Ghost<Seq<Int>>,
}

impl<I: Iterator<Item = i64> + Model> Model for Run<I> {
    type Ty = (<I as Model>::Ty, Seq<Int>, Seq<Int>);
}

#[thrust_macros::context]
#[thrust_macros::requires(
    I::invariant((*r).0)
        && (*r).1.len() == 0
        && (*r).2.len() == 1
        && (*r).2[0] == init
        && forall(|a: Int| forall(|x: Int|
            I::produces((*r).0, x) ==> thrust_macros::pre!(f(a, x))
        ))
)]
#[thrust_macros::ensures(
    result == (!r).2[(!r).1.len()]
        && (!r).2.len() == (!r).1.len() + 1
        && forall(|k: Int|
            0 <= k && k < (!r).1.len()
                ==> thrust_macros::post!(f((!r).2[k], (!r).1[k]), (!r).2[k + 1])
        )
)]
fn fold<I: Iterator<Item = i64> + Model, F: Fn(i64, i64) -> i64>(
    r: &mut Run<I>,
    init: i64,
    f: F,
) -> i64
where
    <I as Model>::Ty: PartialEq,
{
    let rr = r;
    let mut acc = init;
    let mut cnt = 0;
    while let Some(x) = rr.iter.next() {
        thrust_macros::invariant!(
            |rr: &mut Run<I>, r: thrust_models::FnParam<&mut Run<I>>, f: F, acc: i64, cnt: i64|
            I::invariant((*rr).0)
                && !rr == !r.at_entry()
                && 0 <= cnt
                && (*rr).1.len() == cnt
                && (*rr).2.len() == (*rr).1.len() + 1
                && acc == (*rr).2[(*rr).1.len()]
                && forall(|a: Int| forall(|x: Int|
                    I::produces((*rr).0, x) ==> thrust_macros::pre!(f(a, x))
                ))
                && forall(|k: Int|
                    0 <= k && k < (*rr).1.len()
                        ==> thrust_macros::post!(f((*rr).2[k], (*rr).1[k]), (*rr).2[k + 1])
                )
        );
        rr.items = thrust_macros::ghost!(|rr: &mut Run<I>, x: i64| -> Seq<Int> { (*rr).1.push(x) });
        acc = f(acc, x);
        rr.accs = thrust_macros::ghost!(|rr: &mut Run<I>, acc: i64| -> Seq<Int> { (*rr).2.push(acc) });
        cnt += 1;
    }
    acc
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
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        !((*self).start < (*self).end) && *self == !self
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        self.start < self.end
            && self.end == dist.end
            && self.start == item
            && self.start + 1 == dist.start
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // self.start <= item && item < self.end
        self.start <= item && item < self.end
    }
}

// A PARTIAL closure: `x > 0` holds only of what a `1..4` range may produce.
#[thrust_macros::context]
#[thrust_macros::requires(
    Range::invariant((*r).0)
        && (*r).0.start == 1 && (*r).0.end == 4
        && (*r).1.len() == 0
        && (*r).2.len() == 1
        && (*r).2[0] == 0
)]
#[thrust_macros::ensures(
    result == (!r).2[(!r).1.len()] && (!r).2.len() == (!r).1.len() + 1
)]
fn sum_pos(r: &mut Run<Range>) -> i64 {
    let f = thrust_macros::closure!(
        requires(x > 5),
        ensures(result == a + x),
        |a: i64, x: i64| -> i64 { a + x },
    );
    fold(r, 0, f)
}

fn main() {
    let init: i64 = 0;
    let mut r2 = Run {
        iter: Range { start: 1, end: 4 },
        items: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
        accs: thrust_macros::ghost!(|init: i64| -> Seq<Int> { Seq::singleton(init) }),
    };
    sum_pos(&mut r2);
}
