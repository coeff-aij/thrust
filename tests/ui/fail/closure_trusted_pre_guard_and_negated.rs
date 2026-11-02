//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The `requires` reads the closure's precondition positively in a guarded disjunct and negatively in another conjunct, so it states nothing of it: the closure must accept the argument `apply` passes.

#[thrust::trusted]
#[thrust_macros::requires((x < 0 || thrust_macros::pre!(f(x))) && !thrust_macros::pre!(f(1)))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|y: i32| assert!(y > 0), -1)
}
