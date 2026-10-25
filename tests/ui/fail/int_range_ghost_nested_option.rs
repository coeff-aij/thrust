//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An enum inside the payload of the same enum at other arguments, `Option<Option<_>>`, which is
// not a recursive type: under the guard the inner payload is `2^64`; the expected error is the
// obligation on the term.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

fn take(g: Ghost<Option<Option<UIntN<64>>>>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> Option<Option<UIntN<64>>> {
            Some(Some(x + 18446744073709551616u128))
        });
        take(g);
        assert!(x == 1);
    }
}

fn main() {}
