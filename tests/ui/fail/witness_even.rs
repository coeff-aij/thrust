//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;
use thrust_models::Ghost;

#[thrust_macros::predicate]
fn even(n: i64) -> bool {
    exists(|k: i64| n == 2 * k)
}

// `witness` proves `even(m)` by its witness: the goal is the body at `k + 1`, with no `exists`
// to instantiate, and `even(m)` is assumed after it, which the postcondition reads. `k` is the
// witness of the precondition's `even(n)`, named by `choose!`.
// The witness is wrong: `m` is `2 * (k + 1)`, not `2 * (k + 2)`.

#[thrust_macros::requires(even(n) && 0 <= n && n <= 1000)]
#[thrust_macros::ensures(even(result))]
fn add_two(n: i64) -> i64 {
    let k = thrust_macros::choose!(|n: i64| -> i64 { even(n) });
    let m = n + 2;
    thrust_macros::proof_assert!(|m: i64, k: Ghost<i64>| thrust_models::witness(even(m), k + 2));
    m
}

fn main() {
    assert!(add_two(4) == 6);
}
