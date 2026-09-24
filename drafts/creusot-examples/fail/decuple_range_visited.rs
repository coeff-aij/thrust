//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `examples/decuple_range` with its positional property `v[i] == 10 * i`. The iterator
// spec is Creusot's `produces` form plus a unary `produces1` that guards `Map`'s closure
// precondition (the `produces` + unary guard form); `collect` and `FromIterator for Vec<i64>` are
// `traits/collect_visited_seq_i64.rs`'s. Creusot uses `map_inv`; the closure does not read the
// history, so this is plain `map`.
#[thrust_macros::context]
trait Iterator
where
    Self::Item: Model,
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
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces1(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces1(!self, i) ==> Self::produces1(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`, as in `traits/collect_visited_seq_i64.rs`.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty|
        Self::produces(*self, result, pre) && Self::completed(Mut::new(pre, !self))))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized + Model,
        <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty> + PartialEq,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        B::from_iter(self)
    }

    // Reflexivity lemma: the base case of `from_iter`'s loop invariant.
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
    /// `item` is among what `self` may still produce (state-free guard).
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool;
}

struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I, B, F> Iterator for Map<I, F>
where
    I: Iterator + Model,
    <I as Model>::Ty: PartialEq,
    <I as Iterator>::Item: Model,
    <<I as Iterator>::Item as Model>::Ty: PartialEq,
    B: Model,
    F: Fn(I::Item) -> B,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    fn produces_refl(a: &Map<I, F>) {
        I::produces_refl(&a.iter);
    }

    // `F`'s contract is `q_pre_produces_refl_*` / `q_post_produces_refl_*`: the closure call in
    // `next` is emitted under the name of this impl's other method, not `next`'s.
    // self.iter.invariant() && forall e. self.iter.produces1(e) ==> pre!(self.func(e))
    // Creusot's `next_precondition` with the unary guard; `preservation` and `reinitialize` are
    // true for `F: Fn`.
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
        (q_invariant_f4da186d326a37408a3525430033677c<a0> (tuple_proj<a0-a1>.0 self_))
        (forall ((e a5))
        (=> (q_produces1_f4da186d326a37401b2eaa2672dbeeac<a0> (tuple_proj<a0-a1>.0 self_) e)
            (q_pre_produces_refl_f4da186d326a3740800c641d1fc96e06<a1> (tuple_proj<a0-a1>.1 self_) e)))
    )";
        true
    }

    // self.iter.completed() && *self.func == !self.func
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
        (q_completed_f4da186d326a374030348648a393add8<a0> (mut<a0> (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_)) (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))))
        (= (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_)) (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_)))
    )";
        true
    }

    // self.func == o.func && exists s. s.len() == visited.len() && self.iter.produces(s, o.iter)
    // && forall k. post!(self.func(s[k]), visited[k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
        (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 o))
        (exists ((sa (Array Int a5)) (sl Int))
            (and
                (= sl (tuple_proj<Array<Int-a2>-Int>.1 visited))
                (q_produces_f4da186d326a374066294f8cadcb7d04<a0> (tuple_proj<a0-a1>.0 self_) (tuple<Array<Int-a5>-Int> sa sl) (tuple_proj<a0-a1>.0 o))
                (forall ((k Int))
                    (=> (and (<= 0 k) (< k sl))
                        (q_post_produces_refl_f4da186d326a3740800c641d1fc96e06<a1> (tuple_proj<a0-a1>.1 self_) (select sa k) (select (tuple_proj<Array<Int-a2>-Int>.0 visited) k)))))))";
        true
    }
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool {
        "(exists ((j a5))
        (and (q_produces1_f4da186d326a37401b2eaa2672dbeeac<a0> (tuple_proj<a0-a1>.0 self_) j)
             (q_pre_produces_refl_f4da186d326a3740800c641d1fc96e06<a1> (tuple_proj<a0-a1>.1 self_) j)))";
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
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool {
        // self.start <= item && item < self.end
        "(and
            (<= (tuple_proj<Int-Int>.0 self_) item)
            (< item (tuple_proj<Int-Int>.1 self_))
        )";
        true
    }
}

// `FromIterator<A>` reduced to `from_iter`; `Self: Model<Ty = Seq<..>>` lets `result` feed `produces`.
// `&mut I` instead of `I` for the same reason as `collect`. Reflexivity by length: `Vec::new` only
// ensures `length == 0`.
#[thrust_macros::context]
trait FromIterator<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(*iter))]
    #[thrust_macros::ensures(exists(|pre: <I as Model>::Ty|
        I::produces(*iter, result, pre) && I::completed(Mut::new(pre, !iter))))]
    fn from_iter<I: Iterator<Item = A> + Model>(iter: &mut I) -> Self
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq;
}

#[thrust_macros::context]
impl FromIterator<i64> for Vec<i64> {
    fn from_iter<I: Iterator<Item = i64> + Model>(iter: &mut I) -> Vec<i64>
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    {
        let it = iter;
        I::produces_refl(it);
        let mut v: Vec<i64> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<i64>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry() && I::invariant(*it) && I::produces(*iter.at_entry(), v, *it)
            );
            v.push(x);
        }
        v
    }
}

// Creusot: `proof_assert! { forall<i> 0 <= i && i < v.len() ==> v[i] == i * 10 }`.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> result[k] == k * 10 + 1))]
fn decuple_range_visited() -> Vec<i64> {
    let f = thrust_macros::closure!(
        requires(x < 100),
        ensures(result == x * 10),
        |x: i64| -> i64 { x * 10 },
    );
    let mut m = Map {
        iter: Range { start: 0, end: 10 },
        func: f,
    };
    m.collect::<Vec<i64>>()
}

fn main() {}
