//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// As the fail twin, with a closure that changes its state on every call and has no `assert!`.
#[thrust::trusted]
#[thrust_macros::requires(thrust_models::forall(|c: thrust_models::model::Closure<F>, x: thrust_models::model::UInt| thrust_macros::pre!(c(x))))]
#[thrust_macros::ensures(true)]
fn twice<F: FnMut(u64) -> u64>(mut f: F) { f(1); f(1); }
fn main() {
    let mut n = 0u64;
    twice(|_x: u64| { n += 1; 0 });
}
