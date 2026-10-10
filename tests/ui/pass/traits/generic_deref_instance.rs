//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use std::ops::Deref;
use thrust_models::forall;

#[derive(Clone, Copy)]
struct Wrapper(u64);

impl thrust_models::Model for Wrapper {
    type Ty = (u64,);
}

impl Deref for Wrapper {
    type Target = u64;

    #[thrust::trusted]
    fn deref(&self) -> &u64 {
        &self.0
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == (*w).0)]
fn _extern_spec_wrapper_deref(w: &Wrapper) -> &u64 {
    <Wrapper as Deref>::deref(w)
}

#[thrust_macros::requires(forall(|r: &u64| thrust_macros::post!(<F as Deref>::deref(&x), r) ==> *r > 0))]
#[thrust_macros::ensures(result > 0)]
fn read<F: Deref<Target = u64> + Copy>(x: F) -> u64 {
    *x
}

fn main() {
    let v = read(Wrapper(5));
    assert!(v > 0);
}
