//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of `Option::zip` that fixes `U = u8` and keeps `T` is the contract of the calls
// at `U = u8`, in place of the generic spec, which it must refine over `T`.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_zip<T: thrust_models::Model, U: thrust_models::Model>(
    a: Option<T>,
    b: Option<U>,
) -> Option<(T, U)> {
    Option::zip(a, b)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(a != None)]
#[thrust_macros::ensures(b == None ==> result == None)]
fn _extern_spec_zip_byte<T: thrust_models::Model>(
    a: Option<T>,
    b: Option<u8>,
) -> Option<(T, u8)> {
    Option::zip(a, b)
}

fn main() {
    let z = Some(1i32).zip(None::<u8>);
    assert!(z.is_none());
}
