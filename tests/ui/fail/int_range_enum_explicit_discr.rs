//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An enum with explicit, negative discriminants: the payload facts of a value are guarded by its
// discriminant as declared, so the postcondition's quantifier over `u8` rules out every `A`.
use thrust_models::forall;

#[repr(i8)]
pub enum E {
    B = 7,
    A(u8) = -3,
}

impl thrust_models::Model for E {
    type Ty = Self;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|i: u8| result != E::A(i)))]
fn not_a() -> E {
    unimplemented!()
}

fn main() {
    let r = not_a();
    assert!(matches!(r, E::A(_)));
}
