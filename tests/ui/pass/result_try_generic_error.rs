//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1

// `?` at an error type that names a type parameter: the conversion is the reflexive `From`,
// resolved under the function's bounds.
enum Failure<F> {
    Overflow,
    At(F),
}

impl<F: thrust_models::Model> thrust_models::Model for Failure<F> {
    type Ty = Failure<<F as thrust_models::Model>::Ty>;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((r == Err(Failure::Overflow)) ==> (result == Err(Failure::Overflow)))]
fn inc<F: thrust_models::Model>(r: Result<i32, Failure<F>>) -> Result<i32, Failure<F>> {
    let x = r?;
    Ok(x)
}

fn main() {
    let r: Result<i32, Failure<u8>> = inc(Err(Failure::Overflow));
    assert!(matches!(r, Err(Failure::Overflow)));
}
