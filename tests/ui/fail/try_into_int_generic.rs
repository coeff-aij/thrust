//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// A conversion at a type parameter bounded by `TryIntoSpec` is described by its predicates,
// which a caller at a concrete type sees through that type's impl.
use std::convert::TryInto;

#[thrust_macros::requires(T::fits(x))]
#[thrust_macros::ensures(T::converts_to(x, result))]
fn to_u64<T: TryIntoSpec<u64>>(x: T) -> u64 {
    x.try_into().ok().unwrap()
}

fn main() {
    let a: i32 = 8;
    assert!(to_u64(a) == 9);
}
