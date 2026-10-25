//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A trusted consumer of an iterator, whose contract does not require the iterator's `inv`, runs
// `Map`'s closure: its precondition is required where the `Map` is made, here of unbounded items.
#[thrust::trusted]
#[thrust::callable]
fn consume<I: IteratorSpec<Item = usize>>(it: I) -> usize
where
    I::Item: thrust_models::Model,
{
    it.sum()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn count_small(v: &[u64]) -> usize {
    consume(v.iter().map(|w| { assert!(*w < 10); 1usize }))
}

fn main() {}
