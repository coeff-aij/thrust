//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_main_result.rs`: `main`'s error type is `()`, so `S`'s ignored `fmt`
// is not reached. A hand-written `Debug::fmt` is not analyzable, so the twin keeps it ignored.

struct S;

impl std::fmt::Debug for S {
    #[thrust::ignored]
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

fn main() -> Result<(), ()> {
    Ok(())
}
