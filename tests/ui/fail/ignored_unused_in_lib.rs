//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A verified function that unwraps a `Result` with an error of `&S` can run `S`'s ignored
// `Debug::fmt`, which `unwrap` prints on its way to a panic.

pub struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl std::fmt::Debug for S {
    #[thrust::ignored]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { //~ ERROR: a verified function can run it
        write!(f, "S")
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
pub fn show(s: &S) -> usize {
    let r: Result<usize, &S> = Ok(s.0 as usize);
    r.unwrap()
}
