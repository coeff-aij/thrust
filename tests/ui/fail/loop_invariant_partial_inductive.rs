//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `partial_invariant!` is checked, not assumed: the `fail` twin's body does not preserve it,
// and assuming it would prove the postcondition.

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
fn count(n: i64) -> i64 {
    let mut i = 0_i64;
    let mut s = 0_i64;
    while i < n {
        thrust_macros::partial_invariant!(|i: i64, s: i64| s == i);
        s += 2;
        i += 1;
    }
    s
}

fn main() {}
