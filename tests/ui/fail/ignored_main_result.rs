//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `main` returns `Err(S)`, which the runtime's `start` reports with `S`'s ignored `Debug::fmt`;
// the `start` lang item at `main`'s return type is a root, as for rustc's collector.

struct S;

impl std::fmt::Debug for S {
    #[thrust::ignored]
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { //~ ERROR: a verified function can run it
        Ok(())
    }
}

fn main() -> Result<(), S> {
    Err(S)
}
