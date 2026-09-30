//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744 THRUST_TRY_SPECS=1

// The case study's `DenseBitSet` with the model (domain size, cardinality): the struct is opaque,
// its bodies are trusted, and it keeps its derived `Hash`. `iter` yields as many items as the
// cardinality, so a loop over it is bounded by it.

use std::marker::PhantomData;
use thrust_models::model::{Int, Seq};

#[derive(Hash)]
#[thrust::opaque]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<u64>,
    marker: PhantomData<T>,
}

impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = (Int, Int);
}

#[thrust::opaque]
pub struct BitIter<'a, T> {
    word: u64,
    offset: usize,
    words: std::slice::Iter<'a, u64>,
    marker: PhantomData<T>,
}

impl<'a, T> thrust_models::Model for BitIter<'a, T> {
    type Ty = Int;
}

#[thrust_macros::context]
impl<T> DenseBitSet<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == domain_size && result.1 == 0)]
    pub fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        let num_words = domain_size.div_ceil(64);
        DenseBitSet { domain_size, words: vec![0; num_words], marker: PhantomData }
    }

    #[thrust::trusted]
    #[thrust_macros::requires(elem < (*self).0)]
    #[thrust_macros::ensures(
        (!self).0 == (*self).0
            && (*self).1 <= (!self).1 && (!self).1 <= (*self).1 + 1 && (!self).1 <= (!self).0
    )]
    pub fn insert(&mut self, elem: usize) {
        self.words[elem / 64] |= 1 << (elem % 64);
    }

    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).1 && 0 <= (*self).1)]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter { word: 0, offset: usize::MAX - 63, words: self.words.iter(), marker: PhantomData }
    }
}

impl<'a, T> Iterator for BitIter<'a, T> {
    type Item = usize;

    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<usize> {
        loop {
            if self.word != 0 {
                let bit_pos = self.word.trailing_zeros() as usize;
                self.word ^= 1 << bit_pos;
                return Some(bit_pos + self.offset);
            }
            self.word = *self.words.next()?;
            self.offset = self.offset.wrapping_add(64);
        }
    }
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> IteratorSpec for BitIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        0 <= o && o + visited.len() == self
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

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*set).1)]
fn count<T: thrust_models::Model>(set: &DenseBitSet<T>) -> usize
where
    T::Ty: PartialEq,
{
    let mut n = 0;
    let mut it = set.iter();
    while let Some(_) = it.next() {
        thrust_macros::invariant!(
            |it: BitIter<T>, n: usize, set: thrust_models::FnParam<&DenseBitSet<T>>|
                0 <= it && n + it == (*set.at_entry()).1
        );
        n += 1;
    }
    n
}

fn main() {
    let mut set: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    set.insert(3);
    set.insert(70);
    assert!(count(&set) <= 1);
}
