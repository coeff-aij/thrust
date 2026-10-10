//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A full `invariant!` is the loop head's whole invariant, so it restates what
// `loop_invariant_partial.rs` leaves to inference.

#[thrust_macros::requires(n >= 0 && m >= 1)]
#[thrust_macros::ensures(2 * result.0 == n * (n - 1) && result.1 >= 1)]
fn sum_below(n: i64, m: i64) -> (i64, i64) {
    let mut i = 0_i64;
    let mut s = 0_i64;
    let mut p = 1_i64;
    while i < n {
        thrust_macros::invariant!(|i: i64, s: i64, p: i64, n: i64, m: i64|
            2 * s == i * (i - 1) && 0 <= i && i <= n && p >= 1 && m >= 1);
        s += i;
        i += 1;
        p = p * m;
    }
    (s, p)
}

fn main() {}
