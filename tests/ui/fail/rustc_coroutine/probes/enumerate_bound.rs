//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744 THRUST_TRY_SPECS=1

// The enumerate position over a bit-set iterator stays below the domain size: `BitIter`'s model
// is (bound, count), as in tests/ui/pass/rustc_coroutine/eligibility.rs.

use thrust_models::forall;
use thrust_models::model::Int;

pub struct DenseBitSet {
    domain_size: usize,
    marker: (),
}

impl thrust_models::Model for DenseBitSet {
    type Ty = (Int, ());
}

pub struct BitIter {}

impl thrust_models::Model for BitIter {
    type Ty = (Int, Int);
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust_macros::ensures(result.0 == domain_size)]
    fn new_empty(domain_size: usize) -> DenseBitSet {
        DenseBitSet { domain_size, marker: () }
    }

    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result.0 == (*self).0 && result.1 == 0)]
    fn iter(&self) -> BitIter {
        BitIter {}
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
        0 <= self.1 && self.1 <= self.0
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        self.0 == o.0
            && o.1 == self.1 + visited.len()
            && o.1 <= self.0
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] < self.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        true
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::requires(idx < n - 1)]
#[thrust_macros::ensures(true)]
fn need(idx: usize, n: usize) {}

fn test(n: usize) {
    let set: DenseBitSet = DenseBitSet::new_empty(n);
    let mut it = set.iter().enumerate();
    while let Some((idx, _local)) = it.next() {
        thrust_macros::invariant!(|it: std::iter::Enumerate<BitIter>, n: usize|
            it.0.0 == n && it.1 == it.0.1 && 0 <= it.1 && it.1 <= n);
        need(idx, n);
    }
}

fn main() {
    test(5);
}
