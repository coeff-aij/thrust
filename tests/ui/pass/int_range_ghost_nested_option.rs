//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the fail file: the inner payload is in range.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

fn take(g: Ghost<Option<Option<UIntN<64>>>>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> Option<Option<UIntN<64>>> {
            Some(Some(x))
        });
        take(g);
        assert!(x == 0);
    }
}

fn main() {}
