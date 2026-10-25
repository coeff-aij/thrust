//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Soundness check for the range of a tuple element: under the guard, the ghost term's first
// element is `2^64` (model arithmetic is unbounded). The ghost value has type
// `(UIntN<64>, UIntN<64>)`, whose elements are assumed below `2^64`. If the ghost were introduced
// without an obligation, the contradiction would verify the `assert!` vacuously; the expected error
// is the obligation on the term.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

fn take(g: Ghost<(UIntN<64>, UIntN<64>)>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> (UIntN<64>, UIntN<64>) {
            (x + 18446744073709551616u128, x)
        });
        take(g);
        assert!(x == 1);
    }
}

fn main() {}
