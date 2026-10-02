//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::{exists, forall, model::Int};

// The closures in `client` have no contract, so at the call their `pre!` and `post!` are unknowns
// and `compose`'s body is analyzed again with them. The intermediate value is neither the argument
// nor the result, so the `ensures` names it under an existential, and its check is a clause with
// the two postcondition unknowns under an existential in the head.
#[thrust_macros::requires(thrust_macros::pre!(f(x))
    && forall(|y: Int| !thrust_macros::post!(f(x), y) || thrust_macros::pre!(g(y))))]
#[thrust_macros::ensures(exists(|y: Int| thrust_macros::post!(f(x), y) && thrust_macros::post!(g(y), result)))]
fn compose<F: Fn(i64) -> i64, G: Fn(i64) -> i64>(x: i64, f: F, g: G) -> i64 {
    g(f(x))
}

#[thrust_macros::requires(0 <= x && x < 1000)]
#[thrust_macros::ensures(result > 2)]
fn client(x: i64) -> i64 {
    compose(x, |a: i64| a + 1, |b: i64| b * 2)
}

fn main() {}
