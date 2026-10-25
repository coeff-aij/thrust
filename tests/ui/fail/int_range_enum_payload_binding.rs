//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The payload of an enum value is in its type's range wherever the value is bound, not only where
// a `match` takes it out: the quantifier over `UIntN<64>` in `none`'s postcondition rules out every
// `Some` the result can be, so it is not a `Some`, which this file asserts.
use thrust_models::forall;
use thrust_models::model::UIntN;

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|i: UIntN<64>| result != Some(i)))]
fn none() -> Option<usize> {
    unimplemented!()
}

fn main() {
    let r = none();
    assert!(matches!(r, Some(_)));
}
