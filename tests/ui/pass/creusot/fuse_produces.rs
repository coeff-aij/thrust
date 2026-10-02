//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, forall, Model};

// The generic `Fuse` of the current Creusot (3620de437, `examples/iterators/07_fuse.rs`): state
// `Option<I>`, its `completed` and `produces`, and the `FusedIterator::is_fused` law.
// fuse_produces_result.rs is the 2022 artifact's version, with state `Result<I, Ghost<I>>`.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, which every impl
// inherits and Thrust checks at each impl (Creusot restates them per impl with empty bodies), and
// `next` with Creusot's contract.
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
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {}

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

// Creusot's `FusedIterator`: once `completed`, the iterator produces nothing and stays put.
#[thrust_macros::context]
trait FusedIterator: Iterator
where
    Self: Model,
    Self::Item: Model,
    <Self as Model>::Ty: PartialEq,
{
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::completed(s))]
    #[thrust_macros::requires(Self::produces(!s, steps, *next))]
    #[thrust_macros::ensures(steps == Seq::empty() && !s == *next)]
    fn is_fused(s: &mut Self, steps: Seq<<Self::Item as Model>::Ty>, next: &Self) {}
}

pub struct Fuse<I> {
    iter: Option<I>,
}

impl<I: Model> Model for Fuse<I> {
    type Ty = Fuse<<I as Model>::Ty>;
}

// For `==` on a `Fuse` in `is_fused`.
impl<I: Model + PartialEq> PartialEq for Fuse<I> {
    fn eq(&self, other: &Fuse<I>) -> bool {
        self.iter == other.iter
    }
}

#[thrust_macros::context]
impl<I> Iterator for Fuse<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <Fuse<I> as Model>::Ty: Model<Ty = <Fuse<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                None => {
                    self.iter = None;
                    None
                }
                x => x,
            },
        }
    }



    // Creusot: `(self.iter == None || exists<it: &mut I> it.completed() && self.iter == Some(*it))
    // && (^self).iter == None`.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).iter == None
            || exists(|i: <I as Model>::Ty| exists(|j: <I as Model>::Ty|
                (*self).iter == Some(i) && I::completed(Mut::new(i, j)))))
            && (!self).iter == None
    }

    // Creusot's `match self.iter`: from `None` nothing is produced, and from `Some(i)` only to a
    // `Some(k)` that `i` produces.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (self.iter == None && visited == Seq::empty() && o.iter == self.iter)
            || exists(|i: <I as Model>::Ty| exists(|k: <I as Model>::Ty|
                self.iter == Some(i) && o.iter == Some(k) && I::produces(i, visited, k)))
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.iter == None || exists(|i: <I as Model>::Ty| self.iter == Some(i) && I::invariant(i))
    }
}

#[thrust_macros::context]
impl<I> FusedIterator for Fuse<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <Fuse<I> as Model>::Ty: Model<Ty = <Fuse<I> as Model>::Ty> + PartialEq,
{
}

fn main() {}
