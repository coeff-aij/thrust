//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A user enum whose field is fixed in its definition: under the guard, the ghost term's payload is
// `2^64` (model arithmetic is unbounded), and the payload of `E::A` is assumed below `2^64`; the
// expected error is the obligation on the term.
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
            E::A(x + 18446744073709551616u128)
        });
        take(g);
        assert!(x == 1);
    }
}

fn main() {}
