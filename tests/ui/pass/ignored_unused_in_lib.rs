//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_unused_in_lib.rs`: a library whose verified functions do not run
// `S`'s `Debug::fmt` may leave it ignored, though the impl is public.

pub struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl std::fmt::Debug for S {
    #[thrust::ignored]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "S")
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
pub fn show(s: &S) -> usize {
    let r: Result<usize, usize> = Ok(s.0 as usize);
    r.unwrap()
}
