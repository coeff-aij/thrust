//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the fail file: the ghost term's payload is in range, so its obligation holds.
use thrust_models::model::UIntN;
use thrust_models::Ghost;

pub enum E {
    A(UIntN<64>),
    B,
}

impl thrust_models::Model for E {
    type Ty = Self;
}

fn take(g: Ghost<E>) {
    let _ = g;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let g = thrust_macros::ghost!(|x: usize| -> E {
            E::A(x)
        });
        take(g);
        assert!(x == 0);
    }
}

fn main() {}
