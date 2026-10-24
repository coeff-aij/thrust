//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the soundness check of the same name: the ghost term's integers are in range, so its
// obligation holds and the assertion is reached only where it holds.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

fn take(g: Ghost<(UIntN<64>, UIntN<64>)>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> (UIntN<64>, UIntN<64>) { (x, x) });
        take(g);
        assert!(x == 0);
    }
}

fn main() {}
