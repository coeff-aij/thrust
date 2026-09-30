//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall};
pub struct Wrapped<T> {
    raw: Vec<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrapped<T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
impl<T> Wrapped<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((!self).len() == (*self).len() + 1)]
    fn push(&mut self, value: T) {
        self.raw.push(value);
    }

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == raw)]
    fn from_raw(raw: Vec<T>) -> Wrapped<T> {
        Wrapped { raw }
    }
}


// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// the collection: the collection is what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(iter))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(iter, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
fn collect_wrapped<T, J>(iter: J) -> Wrapped<T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: IteratorSpec<Item = T>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::inv(it) && J::produces(iter.at_entry(), v, it)
        );
        v.push(x);
    }
    Wrapped::from_raw(v)
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
fn collect_all(xs: &[u32]) -> Wrapped<&u32> {
    collect_wrapped(iter_of(xs))
}

fn main() {}
