//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic enum's field fixed in its definition (the second of `W::A`), at an instance: under the
// guard the ghost term puts `2^64` there; the expected error is the obligation on the term.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

pub enum W<T> {
    A(T, UIntN<64>),
    B,
}

impl<T> thrust_models::Model for W<T> {
    type Ty = Self;
}

fn take(g: Ghost<W<UIntN<8>>>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize, y: u8) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize, y: u8| -> W<UIntN<8>> {
            W::A(y, x + 18446744073709551616u128)
        });
        take(g);
        // Keeps `y` live up to the ghost term, which reads it.
        let z = y;
        assert!(z == y);
        assert!(x == 1);
    }
}

fn main() {}
