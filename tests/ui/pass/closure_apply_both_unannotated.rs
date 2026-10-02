//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::forall;

// The closure in `main` has no contract, so at the call its `pre!` and `post!` are unknowns and
// `apply_both`'s body is analyzed again with them. Its `requires` is then assumed with the
// precondition unknown under a universal quantifier in a clause body.
#[thrust_macros::requires(forall(|j: i64| thrust_macros::pre!(f(j))))]
#[thrust_macros::ensures(thrust_macros::post!(f(a), result.0) && thrust_macros::post!(f(b), result.1))]
fn apply_both<F: Fn(i64) -> i64>(f: &F, a: i64, b: i64) -> (i64, i64) {
    (f(a), f(b))
}

fn main() {
    let f = |x: i64| x + 1;
    let (u, v) = apply_both(&f, 1, 2);
    assert!(u + v == 5);
}
