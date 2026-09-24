//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// Creusot's `common.rs` iterator spec: ternary `produces(self, visited, o)`, `completed`, and the
// laws applied as ensures on `next`; reflexivity is also a callable law (`produces_refl`).
// `take_count` is a call site of the generic `Take` (`traits/take.rs`) at `Take<Range>`.
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
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*self, s, *self)))]
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && s.len() == 1 && s[0] == i ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i| forall(|t: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && Self::produces(a, s, *self) && t == s.push(i) ==> Self::produces(a, t, !self))))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity as a callable law: an adapter that answers without touching its inner
    // iterator (`Take` at `n == 0`) has no `next` ensures of the inner to take it from.
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
}

pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I: Model> Model for Take<I> {
    type Ty = (<I as Model>::Ty, Int);
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Take<I> as Model>::Ty: Model<Ty = <Take<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            I::produces_refl(&self.iter);
            None
        }
    }

    fn produces_refl(a: &Take<I>) {
        I::produces_refl(&a.iter);
    }

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
            (q_invariant_697f611e1c8a799099f5cab24a2a3c2a<a0> (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0)
        )";
        true
    }

    // (*self.n == 0 && *self == !self) ||
    // (*self.n > 0 && *self.n == !self.n + 1 && self.iter.completed())
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(or
            (and
                (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0)
                (= (mut_current<Tuple<a0-Int>> self_) (mut_final<Tuple<a0-Int>> self_)))
            (and
                (> (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0)
                (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_))
                   (+ (tuple_proj<a0-Int>.1 (mut_final<Tuple<a0-Int>> self_)) 1))
                (q_completed_697f611e1c8a7990df91d46c1657fcab<a0>
                    (mut<a0>
                        (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                        (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))))))";
        true
    }

    // self.n == o.n + visited.len() && self.iter.produces(visited, o.iter)
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
            (= (tuple_proj<a0-Int>.1 self_)
               (+ (tuple_proj<a0-Int>.1 o) (tuple_proj<Array<Int-a1>-Int>.1 visited)))
            (q_produces_697f611e1c8a799049ce63996d440b34<a0> (tuple_proj<a0-Int>.0 self_) visited (tuple_proj<a0-Int>.0 o)))";
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

    fn produces_refl(a: &Range) {}

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
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
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

// A generic `Take` at `Take<Range>`, drained in a loop: at most `n` items come out, whatever the
// range. The loop invariant reads the adapter's counter through its model.
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result <= n)]
fn take_count(start: i64, end: i64, n: usize) -> usize {
    let mut t = Take { iter: Range { start, end }, n };
    let mut cnt: usize = 0;
    while let Some(_x) = t.next() {
        thrust_macros::invariant!(|t: Take<Range>, cnt: usize, n: thrust_models::FnParam<usize>|
            cnt + t.1 == n.at_entry() && t.1 >= 0 && Take::<Range>::invariant(t));
        cnt += 1;
    }
    cnt
}

fn main() {}
