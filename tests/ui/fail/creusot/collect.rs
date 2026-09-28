//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::{exists, forall};
use thrust_models::model::Mut;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// Creusot's `collect` on the shared iterator specification, with a `FromIterator<T> for Vec<T>`.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, proved by each
// impl, and `next` with Creusot's contract.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`; `self` in the ensures is the entry value.
    #[thrust_macros::requires(Self::invariant(self))]
    #[thrust_macros::ensures(exists(|pre: <Self as Model>::Ty| exists(|fin: <Self as Model>::Ty|
        Self::produces(self, result, pre) && Self::completed(Mut::new(pre, fin)))))]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
        <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty> + PartialEq,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        B::from_iter(self)
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

    fn produces_trans(a: &Range, ab: Seq<<Self::Item as Model>::Ty>, b: &Range, bc: Seq<<Self::Item as Model>::Ty>, c: &Range) {}

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.resolve() && self.start >= self.end
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        // self.end == o.end && self.start <= o.start
        // && (visited.len() > 0 ==> o.start <= o.end)
        // && visited.len() == o.start - self.start
        // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

// `FromIterator<A>` reduced to `from_iter`; `Self: Model<Ty = Seq<..>>` lets `result` feed `produces`.
// Reflexivity by length: `Vec::new` only ensures `length == 0`.
#[thrust_macros::context]
trait FromIterator<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(iter))]
    #[thrust_macros::ensures(exists(|pre: <I as Model>::Ty| exists(|fin: <I as Model>::Ty|
        I::produces(iter, result, pre) && I::completed(Mut::new(pre, fin)))))]
    fn from_iter<I: Iterator<Item = A> + Model>(iter: I) -> Self
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq;
}

#[thrust_macros::context]
impl<T: Model> FromIterator<T> for Vec<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
    fn from_iter<I: Iterator<Item = T> + Model>(iter: I) -> Vec<T>
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    {
        let mut it = iter;
        I::produces_refl(&it);
        let v: Vec<T> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: I, v: Vec<T>, iter: thrust_models::FnParam<I>|
                I::invariant(it) && I::produces(iter.at_entry(), v, it)
            );
        }
        v
    }
}

#[thrust_macros::requires(start <= end)]
#[thrust_macros::ensures(result.len() == end - start && forall(|k: Int| 0 <= k && k < result.len() ==> result[k] == start + k))]
fn collect_range(start: i64, end: i64) -> Vec<i64> {
    let r = Range { start, end };
    r.collect::<Vec<i64>>()
}

fn main() {}
