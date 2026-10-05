//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `pass/int_range_enum_payload.rs`: `pick` may return `Some(9)`.
use thrust_models::forall;
use thrust_models::model::UIntN;

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|i: UIntN<64>| result == Some(i) ==> i < 10))]
fn pick() -> Option<usize> {
    unimplemented!()
}

fn main() {
    match pick() {
        Some(e) => assert!(e < 9),
        None => {}
    }
}
