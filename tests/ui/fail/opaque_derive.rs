//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// `PartialEq::eq`'s contract equates the models, which the derived body, comparing the fields,
// does not establish: the abstraction need not be injective.

use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use thrust_models::model::Int;

#[derive(Hash, PartialEq)] //~ ERROR: the derived `PartialEq::eq` accesses the field `domain_size`
#[thrust::opaque]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<u64>,
    marker: PhantomData<T>,
}

impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = (Int, Int);
}

#[thrust_macros::context]
impl<T> DenseBitSet<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == domain_size && result.1 == 0)]
    fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        DenseBitSet { domain_size, words: vec![0; domain_size.div_ceil(64)], marker: PhantomData }
    }
}

struct CountingHasher {
    writes: i64,
}

impl thrust_models::Model for CountingHasher {
    type Ty = CountingHasher;
}

impl Hasher for CountingHasher {
    fn write(&mut self, _bytes: &[u8]) {
        self.writes += 1;
    }

    fn finish(&self) -> u64 {
        0
    }
}

fn main() {
    let s: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    let mut h = CountingHasher { writes: 0 };
    s.hash(&mut h);
    assert!(h.writes >= 0 || h.writes < 0);
}
