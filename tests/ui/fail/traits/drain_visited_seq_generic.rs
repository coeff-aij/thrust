//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

// Creusot's common.rs: ternary `produces(self, visited, o)` over a Seq, `completed(&mut self)`,
// and `next`'s ensures `Some(v) ==> produces(*self, [v], ^self)`.
#[thrust_macros::context]
trait Iterator
where
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    // `completed` is abstract here, so a caller reasoning about `!self` needs the resolution
    // spelled out: an exhausted iterator is left untouched.
    #[thrust_macros::ensures(result == None ==> *self == !self)]
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>| result == Some(i) && s.len() == 1 && s[0] == i ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        forall(|t: Seq<<Self::Item as Model>::Ty>|
            result == Some(i) && Self::produces(a, s, *self) && t == s.push(i) ==> Self::produces(a, t, !self))))))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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
        let item = self.start;
        self.start += 1;
        if item < self.end {
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
        // self.resolve() && self.start >= self.end
        "(and
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
            (>= (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_)))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<Int>, o: Self) -> bool {
        // self.end == o.end && self.start <= o.start
        // && (visited.len() > 0 ==> o.start <= o.end)
        // && visited.len() == o.start - self.start
        // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
        "(and
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 o))
            (<= (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.0 o))
            (=> (> (tuple_proj<Array<Int-Int>-Int>.1 visited) 0)
                (<= (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.1 o)))
            (= (tuple_proj<Array<Int-Int>-Int>.1 visited)
               (- (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.0 self_)))
            (forall ((zi Int))
                (=> (and (<= 0 zi) (< zi (tuple_proj<Array<Int-Int>-Int>.1 visited)))
                    (= (select (tuple_proj<Array<Int-Int>-Int>.0 visited) zi)
                       (+ (tuple_proj<Int-Int>.0 self_) zi))))
        )";
        true
    }
}

// Creusot's `for x in iter` with `#[invariant(... produced ...)]`: the produced history is a
// ghost field, the loop invariant is `init.produces(produced, iter)`, and preservation comes
// from `next`'s one-step ensures instead of a `produces_trans` law.
struct Run<I: Iterator + Model>
where
    I::Item: Model,
{
    iter: I,
    init: Ghost<Seq<<I as Model>::Ty>>,
    produced: Ghost<Seq<<I::Item as Model>::Ty>>,
}

impl<I: Iterator + Model> Model for Run<I>
where
    I::Item: Model,
{
    type Ty = (<I as Model>::Ty, Seq<<I as Model>::Ty>, Seq<<I::Item as Model>::Ty>);
}

#[thrust_macros::context]
#[thrust_macros::requires(
    I::invariant((*r).0) && (*r).1.len() == 1 && (*r).1[0] == (*r).0 && (*r).2.len() == 0 && I::produces((*r).1[0], (*r).2, (*r).0)
)]
#[thrust_macros::ensures((!r).1 == (*r).1 && I::produces((!r).1[0], (!r).2, (!r).0))]
fn drain<I: Iterator + Model>(r: &mut Run<I>)
where
    I::Item: Model,
    <I as Model>::Ty: Model + PartialEq,
    <I::Item as Model>::Ty: PartialEq,
{
    let rr = r;
    while let Some(x) = rr.iter.next() {
        thrust_macros::invariant!(
            |rr: &mut Run<I>, r: thrust_models::FnParam<&mut Run<I>>|
            I::invariant((*rr).0)
                && !rr == !r.at_entry()
                && (*rr).1 == (*r.at_entry()).1
                && I::produces((*rr).1[0], (*rr).2, (*rr).0)
        );
        rr.produced = thrust_macros::ghost!(
            |rr: &mut Run<I>, x: I::Item| -> Seq<<I::Item as Model>::Ty> { (*rr).2.push(x) }
        );
    }
}

fn main() {}
