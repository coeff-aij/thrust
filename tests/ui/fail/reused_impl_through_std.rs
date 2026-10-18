//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `W`'s generic `clone` derefs its field, taking `F`'s `deref` to accept any value. `Option`'s std
// `clone` runs it at `Wrapper`, whose `deref` requires a positive field, so `W::clone` at
// `Wrapper` is checked as an instance of its generic contract, as a direct call is: `Wrapper(0)`
// panics.

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
        if self.0 == 0 {
            panic!()
        }
        &self.0
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires((*w).0 > 0)]
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
