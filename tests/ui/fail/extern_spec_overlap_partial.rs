//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of `Option::zip` that fixes `U = u8` and keeps `T` is the contract of the
// calls at `U = u8`. A second spec fixing `T = u64` instead would cover `zip::<u64, u8>` too,
// although neither includes the other, and is rejected (`fail/extern_spec_overlap_partial.rs`).

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(b == None ==> result == None)]
fn _extern_spec_zip_byte<T: thrust_models::Model>(
    a: Option<T>,
    b: Option<u8>,
) -> Option<(T, u8)> {
    Option::zip(a, b)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_zip_word<U: thrust_models::Model>( //~ ERROR: both cover some of its instances
    a: Option<u64>,
    b: Option<U>,
) -> Option<(u64, U)> {
    Option::zip(a, b)
}

fn main() {
    let z = Some(1i32).zip(None::<u8>);
    assert!(z.is_none());
}
