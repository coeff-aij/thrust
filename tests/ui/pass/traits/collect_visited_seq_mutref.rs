//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::{exists, forall};
use thrust_models::model::Mut;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// The `&mut` variant of `collect_visited_seq`: `collect(&mut self)` / `from_iter(iter: &mut I)`
// and a concrete `FromIterator<i64> for Vec<i64>`, on Creusot's `common.rs`/`range.rs` spec.
// Seq literals are bound before use (`t == s.push(i) ==> ..`): the solver rejects them as arguments.
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
    // `produces_trans` with a singleton second leg, applied at every `next` instead of called.
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && s == Seq::singleton(i) ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i| forall(|t: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && Self::produces(a, s, *self) && t == s.push(i) ==> Self::produces(a, t, !self))))))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`. `&mut self`, not `mut self`: a by-value generic `self`
    // that is moved or `&mut`-reborrowed loses its link to its entry value in the ensures.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty|
        Self::produces(*self, result, pre) && Self::completed(Mut::new(pre, !self))))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized,
        <Self as Model>::Ty: PartialEq,
    {
        B::from_iter(self)
    }

    // Reflexivity lemma: the base case of a loop invariant `iter_old.produces(v, iter)`.
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

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

#[thrust_macros::requires(start <= end)]
#[thrust_macros::ensures(result.len() == end - start && forall(|k: Int| 0 <= k && k < result.len() ==> result[k] == start + k))]
fn collect_range(start: i64, end: i64) -> Vec<i64> {
    let mut r = Range { start, end };
    r.collect::<Vec<i64>>()
}

fn main() {}
