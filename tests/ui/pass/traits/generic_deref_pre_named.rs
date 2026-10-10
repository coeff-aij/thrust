//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pre!` of `Deref::deref` at a type parameter is `true`, so `claim` holds without calling it, and
// the impl an instance reaches has to accept any argument, as for a call.

use std::ops::Deref;

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

#[thrust_macros::ensures(thrust_macros::pre!(<F as Deref>::deref(&x)))]
fn claim<F: Deref<Target = u64> + Copy>(x: F) {}

fn main() {
    claim(Wrapper(0));
}
