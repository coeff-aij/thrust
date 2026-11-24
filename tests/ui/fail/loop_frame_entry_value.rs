//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A written invariant does not name `n`, which the loop does not change, so what held of `n` on
// entry still holds in the loop and after it.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64) {
    let mut i = 0_i64;
    while i < 10 {
        thrust_macros::invariant!(|i: i64| i >= 0);
        i += 1;
    }
    assert!(n > 1);
}

fn main() {}
