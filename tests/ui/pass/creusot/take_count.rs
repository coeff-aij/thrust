//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:0360cb142
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

// `take_count` is a call site of the generic `Take` (`creusot/take.rs`) at `Take<Range>`.

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
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
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

    fn produces_refl(a: &Take<I>) {}

    fn produces_trans(a: &Take<I>, ab: Seq<<Self::Item as Model>::Ty>, b: &Take<I>, bc: Seq<<Self::Item as Model>::Ty>, c: &Take<I>) {}

    // `Take<I>`'s model is the tuple `(<I as Model>::Ty, Int)`, not the named struct: the
    // predicate type-checks against the model, so the components are `.0` (iter) and `.1` (n).
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0) && self.1 >= 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).1 == 0 && (*self).0 == (!self).0 && (*self).1 == (!self).1)
            || ((*self).1 > 0
                && (*self).1 == (!self).1 + 1
                && I::completed(Mut::new((*self).0, (!self).0)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.1 == o.1 + visited.len() && I::produces(self.0, visited, o.0)
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
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

// A generic `Take` at `Take<Range>`, drained in a loop: at most `n` items come out, whatever the
// range. The loop invariant reads the adapter's counter through its model. No Creusot benchmark
// counterpart; it is an extra call site of `creusot/take.rs`'s `Take`.
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
