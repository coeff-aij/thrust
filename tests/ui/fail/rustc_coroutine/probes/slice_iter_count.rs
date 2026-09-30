//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744 THRUST_TRY_SPECS=1

use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall};

impl<I: thrust_models::Model, F> thrust_models::Model for std::iter::Map<I, F> {
    type Ty = <I as thrust_models::Model>::Ty;
}


#[thrust_macros::context]
impl<I, F, B> IteratorSpec for std::iter::Map<I, F>
where
    I: IteratorSpec,
    F: FnMut(I::Item) -> B,
    B: thrust_models::Model,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    B::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<B>, o: Self) -> bool {
        exists(|xs: Seq<<I::Item as thrust_models::Model>::Ty>|
            I::produces(self, xs, o) && xs.len() == visited.len())
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new(*self, !self))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_map<I, B, F>(it: I, f: F) -> std::iter::Map<I, F>
where
    I: IteratorSpec,
    F: FnMut(I::Item) -> B,
    B: thrust_models::Model,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    B::Ty: PartialEq,
{
    <I as Iterator>::map(it, f)
}

pub struct Wrapped<T> {
    raw: Vec<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrapped<T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
trait CollectSpec<A>: FromIterator<A> + thrust_models::Model {
    #[thrust_macros::predicate]
    fn of_len(self, n: Int) -> bool;

    #[thrust_macros::predicate]
    fn stopped(self) -> bool;
}

#[thrust_macros::context]
impl<T: thrust_models::Model> CollectSpec<T> for Wrapped<T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn of_len(self, n: Int) -> bool {
        self.len() == n
    }

    #[thrust_macros::predicate]
    fn stopped(self) -> bool {
        false
    }
}

impl<T> FromIterator<T> for Wrapped<T> {
    fn from_iter<J: IntoIterator<Item = T>>(iter: J) -> Self {
        Wrapped { raw: Vec::from_iter(iter) }
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>, mid: <I as thrust_models::Model>::Ty|
        I::produces(it, visited, mid)
            && I::completed(Mut::new(mid, mid))
            && B::of_len(result, visited.len()))
        || B::stopped(result)
)]
fn _extern_spec_iterator_collect<I, B>(it: I) -> B
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    B: CollectSpec<I::Item>,
    B::Ty: PartialEq,
{
    <I as Iterator>::collect::<B>(it)
}

pub struct SliceIter<'a, T> {
    raw: &'a [T],
    pos: usize,
}

impl<'a, T: thrust_models::Model> thrust_models::Model for SliceIter<'a, T> {
    type Ty = (<&'a [T] as thrust_models::Model>::Ty, Int);
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;

    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<&'a T> {
        None
    }
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> IteratorSpec for SliceIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

fn iter_of(raw: &[u32]) -> SliceIter<'_, u32> {
    SliceIter { raw, pos: 0 }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == (*xs).len() + 1)]
fn collect_all(xs: &[u32]) -> Wrapped<u32> {
    iter_of(xs).map(|x| *x + 1).collect()
}

fn main() {}
