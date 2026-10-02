//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

use thrust_models::{forall, FnParam};

// The closure in `main` has no contract, so at the call its `pre!` and `post!` are unknowns. The
// caller assumes `all`'s `ensures`, which puts the postcondition unknown under a universal
// quantifier in a clause body.
#[thrust_macros::requires(forall(|j: i64| thrust_macros::pre!(p(j))))]
#[thrust_macros::ensures(result ==> forall(|j: i64| 0 <= j && j < n ==> thrust_macros::post!(p(j), true)))]
#[thrust_macros::context]
fn all<P: Fn(i64) -> bool>(p: P, n: i64) -> bool {
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(
            |i: i64, n: i64, p: FnParam<P>|
            0 <= i
                && forall(|j: i64| 0 <= j && j < i ==> thrust_macros::post!(p.at_entry()(j), true))
                && forall(|j: i64| thrust_macros::pre!(p.at_entry()(j)))
        );
        if !p(i) {
            return false;
        }
        i += 1;
    }
    true
}

fn main() {
    let p = |x: i64| x == 0;
    assert!(!all(p, 2));
}
