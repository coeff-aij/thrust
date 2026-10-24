//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// As the fail twin, with the items bounded.
#[thrust::trusted]
#[thrust::callable]
fn consume<I: IteratorSpec<Item = usize>>(it: I) -> usize
where
    I::Item: thrust_models::Model,
{
    it.sum()
}

#[thrust_macros::requires(thrust_models::forall(|i: thrust_models::model::Int| !(0 <= i && i < (*v).len()) || (*v)[i] < 10))]
#[thrust_macros::ensures(true)]
fn count_small(v: &[u64]) -> usize {
    consume(v.iter().map(|w| { assert!(*w < 10); 1usize }))
}

fn main() {}

