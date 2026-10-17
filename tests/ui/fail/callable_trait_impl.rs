//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `#[thrust::callable]` on an impl of a std trait method with a contract in `std.rs`: a call takes
// that contract, so the body is checked against it rather than against `requires(true)
// ensures(true)`.
// Fail twin: a clone that is not the value cloned.

struct S(i64);

impl Clone for S {
    #[thrust::callable]
    fn clone(&self) -> S {
        S(self.0 + 1)
    }
}

fn main() {
    let s = S(1);
    let t = s.clone();
    assert!(t.0 == s.0);
}
