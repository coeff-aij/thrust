//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_mut
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Soundness check for unsigned facts: under the guard, `x - 1` is -1 in the logic (it wraps at run
// time, so the `assert!` fails). The value reaches a position whose type says it is non-negative
// through a generic function instantiated at `usize`. If that position assumed the fact without an
// obligation, the contradiction would verify the `assert!` vacuously; the expected error is the
// obligation where the value enters the position.
fn id<T>(t: T) -> T {
    t
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let r = id(x - 1);
        assert!(r == 7);
    }
}

fn main() {}
