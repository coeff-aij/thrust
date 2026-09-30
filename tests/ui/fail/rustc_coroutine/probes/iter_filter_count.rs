//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744 THRUST_TRY_SPECS=1

use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall};

pub struct DenseBitSet {
    words: Vec<u64>,
}

impl thrust_models::Model for DenseBitSet {
    type Ty = Int;
}

pub struct BitIter {
    word: u64,
}

impl thrust_models::Model for BitIter {
    type Ty = Int;
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result == *self)]
    fn iter(&self) -> BitIter {
        BitIter { word: 0 }
    }
}

impl Iterator for BitIter {
    type Item = usize;
    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<usize> {
        None
    }
}

#[thrust_macros::context]
impl IteratorSpec for BitIter {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        0 <= o && o + visited.len() == self
            && forall(|i: Int| !(0 <= i && i < visited.len()) || 0 <= visited[i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == 0 && *self == !self
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
}

impl<T> Extend<T> for Wrapped<T> {
    #[thrust::trusted]
    fn extend<J: IntoIterator<Item = T>>(&mut self, iter: J) {
        self.raw.extend(iter);
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    exists(|visited: Seq<<J::Item as thrust_models::Model>::Ty>, mid: <J as thrust_models::Model>::Ty|
        J::produces(iter, visited, mid)
            && J::completed(Mut::new(mid, mid))
            && (!slf).len() == (*slf).len() + visited.len())
        && forall(|i: Int| !(0 <= i && i < (*slf).len()) || (!slf)[i] == (*slf)[i])
)]
fn _extern_spec_wrapped_extend<T, J>(slf: &mut Wrapped<T>, iter: J)
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: IteratorSpec + Iterator<Item = T>,
    J::Ty: PartialEq,
    <J::Item as thrust_models::Model>::Ty: PartialEq,
{
    <Wrapped<T> as Extend<T>>::extend(slf, iter)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!v).len() == (*v).len() + *set)]
fn append_bits(set: &DenseBitSet, v: &mut Wrapped<u32>) {
    v.extend(set.iter().map(thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })));
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

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == *set)]
fn collect_bits(set: &DenseBitSet) -> Wrapped<u32> {
    set.iter().map(thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })).collect()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == *set)]
fn collect_some_bits(set: &DenseBitSet) -> Wrapped<usize> {
    set.iter().filter(thrust_macros::closure!(requires(true), ensures(true), |i: &usize| -> bool { *i > 1 })).collect()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!v).len() == (*v).len() + 1 + *set)]
fn push_then_extend(set: &DenseBitSet, v: &mut Wrapped<u32>, tag: u32) {
    v.push(tag);
    v.extend(set.iter().map(thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })));
}

fn main() {}
