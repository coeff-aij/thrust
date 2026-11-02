//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The `requires` reads `g`'s precondition positively in a guarded disjunct and negatively in another conjunct, so it states nothing of it: the solver may choose the precondition smaller than the real one. `g` must accept the argument `t1` passes.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires((x < 0 || thrust_macros::pre!(g(x))) && !thrust_macros::pre!(g(1)))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(-1)
}
