//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the fail file: both fields of the ghost term are in range.
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
            W::A(y, x)
        });
        take(g);
        // Keeps `y` live up to the ghost term, which reads it.
        let z = y;
        assert!(z == y);
        assert!(x == 0);
    }
}

fn main() {}
