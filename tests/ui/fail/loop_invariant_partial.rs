//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `invariant_hint!` is conjoined with the invariant inferred at its loop head: the written
// part gives the nonlinear sum, inference keeps `i <= n` and `p >= 1` from the precondition.

#[thrust_macros::requires(n >= 0 && m >= 1)]
#[thrust_macros::ensures(2 * result.0 == n * (n - 1) && result.1 >= 1)]
#[thrust_macros::context]
fn sum_below(n: i64, m: i64) -> (i64, i64) {
    let mut i = 0_i64;
    let mut s = 0_i64;
    let mut p = 1_i64;
    while i < n {
        thrust_macros::invariant_hint!(|i: i64, s: i64| 2 * s == i * (i + 1));
        s += i;
        i += 1;
        p = p * m;
    }
    (s, p)
}

fn main() {}
