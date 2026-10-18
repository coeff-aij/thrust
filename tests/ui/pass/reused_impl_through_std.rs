//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/reused_impl_through_std.rs`: `Wrapper`'s `deref` accepts any value, as `W`'s
// generic `clone` assumes of `F`'s.

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

struct W<F>(F);

impl<F: thrust_models::Model> thrust_models::Model for W<F> {
    type Ty = W<F::Ty>;
}

impl<F: Deref<Target = u64> + Copy> Clone for W<F> {
    fn clone(&self) -> W<F> {
        let _ = *self.0;
        W(self.0)
    }
}

fn main() {
    let o = Some(W(Wrapper(0)));
    let _p = o.clone();
}
