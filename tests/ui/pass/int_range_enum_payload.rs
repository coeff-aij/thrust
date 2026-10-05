//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An integer a `match` takes out of an enum is in its type's range: `e` is a `usize`, so the
// quantifier over `UIntN<64>` in `pick`'s postcondition applies to it.
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
        Some(e) => assert!(e < 10),
        None => {}
    }
}
