//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Soundness check for the payload range of an enum: under the guard, the ghost term's payload is
// `2^64` (model arithmetic is unbounded). The ghost value has type `Option<UIntN<64>>`, whose
// payload is assumed below `2^64`. If the ghost were introduced without an obligation, the
// contradiction would verify the `assert!` vacuously; the expected error is the obligation on the
// term.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

fn take(g: Ghost<Option<UIntN<64>>>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> Option<UIntN<64>> {
            Some(x + 18446744073709551616u128)
        });
        take(g);
        assert!(x == 1);
    }
}

fn main() {}
