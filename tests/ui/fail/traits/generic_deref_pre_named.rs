//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin with a `deref` that requires a positive field, which `claim`'s postcondition at
// `Wrapper(0)` would then tell `main` of it.

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
#[thrust_macros::requires((*w).0 > 0)]
#[thrust_macros::ensures(*result == (*w).0)]
fn _extern_spec_wrapper_deref(w: &Wrapper) -> &u64 {
    <Wrapper as Deref>::deref(w)
}

#[thrust_macros::ensures(thrust_macros::pre!(<F as Deref>::deref(&x)))]
fn claim<F: Deref<Target = u64> + Copy>(x: F) {}

fn main() {
    claim(Wrapper(0));
}
