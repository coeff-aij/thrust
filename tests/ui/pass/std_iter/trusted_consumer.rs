//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// As the fail twin, with the items bounded and the closure's contract written.
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
    let f = thrust_macros::closure!(
        requires(*w < 10),
        ensures(result == 1),
        |w: &u64| -> usize { 1usize }
    );
    consume(v.iter().map(f))
}

fn main() {}

