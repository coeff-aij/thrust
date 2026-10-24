//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `==` on `Option<&str>` is not equality of models (a `str` has none), so it has no
// specification and the call must be unreachable.
#[thrust::callable]
fn g(a: Option<&str>, b: Option<&str>) -> bool {
    a == b
}

fn main() {}
