//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::forall;
use thrust_models::model::Seq;
use thrust_models::Model;

// Creusot's `common.rs` iterator spec: ternary `produces(self, visited, o)`, `completed`, and the
// laws applied as ensures on `next`; reflexivity is also a callable law (`produces_refl`).
// The generic `Take` is used at a call site: after `take(1)` the second `next` is `None`.
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
    #[thrust_macros::ensures(Self::produces(*self, Seq::empty(), *self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        result == Some(i) && Self::produces(a, s, *self) ==> Self::produces(a, s.push(i), !self)))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity as a callable law: an adapter that answers without touching its inner
    // iterator (`Take` at `n == 0`) has no `next` ensures of the inner to take it from.
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
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

impl<I> Model for Take<I> {
    type Ty = Take<I>;
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
            (q_invariant_8cab213534b4e34b5a37430c4d78e732<a0> (tuple_proj<a0-Int>.0 self_))
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
                (q_completed_8cab213534b4e34b784965d8b6f1934e<a0>
                    (mut<a0>
                        (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                        (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))))))";
        true
    }

    // self.n == o.n + visited.len() + 1 && self.iter.produces(visited, o.iter)
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
            (= (tuple_proj<a0-Int>.1 self_)
               (+ (tuple_proj<a0-Int>.1 o) (seq.len visited) 1))
            (q_produces_8cab213534b4e34ba2deaa5e8313dbff<a0> (tuple_proj<a0-Int>.0 self_) visited (tuple_proj<a0-Int>.0 o)))";
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

fn main() {
    let mut t = Take {
        iter: Range { start: 0, end: 10 },
        n: 1,
    };
    let first = t.next();
    let second = t.next();
    assert!(matches!(first, Some(0)));
    assert!(matches!(second, None));
}
