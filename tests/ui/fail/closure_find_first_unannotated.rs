//@ignore-on-host: not yet verifiable, the solver gives no answer within 300 s (fptprove thrust-benchmarks unsolved/uchc_find_first_closure_post_2026-10-03/)
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300

use thrust_models::{forall, FnParam};

// The closure in `main` has no contract, so at the call its `pre!` and `post!` are unknowns. The
// caller assumes `find_first`'s second `ensures`, which puts the postcondition unknown under a
// universal quantifier in a clause body.
#[thrust_macros::requires(0 <= n)]
#[thrust_macros::requires(forall(|j: i64| thrust_macros::pre!(p(j))))]
#[thrust_macros::ensures(0 <= result && result <= n)]
#[thrust_macros::ensures(forall(|j: i64| 0 <= j && j < result ==> thrust_macros::post!(p(j), false)))]
#[thrust_macros::ensures(result < n ==> thrust_macros::post!(p(result), true))]
#[thrust_macros::context]
fn find_first<P: Fn(i64) -> bool>(p: P, n: i64) -> i64 {
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(
            |i: i64, n: i64, p: FnParam<P>|
            0 <= i && i <= n
                && forall(|j: i64| 0 <= j && j < i ==> thrust_macros::post!(p.at_entry()(j), false))
                && forall(|j: i64| thrust_macros::pre!(p.at_entry()(j)))
        );
        if p(i) {
            return i;
        }
        i += 1;
    }
    n
}

fn main() {
    let r = find_first(|x: i64| 3 * x >= 10, 10);
    assert!(r == 3);
}
